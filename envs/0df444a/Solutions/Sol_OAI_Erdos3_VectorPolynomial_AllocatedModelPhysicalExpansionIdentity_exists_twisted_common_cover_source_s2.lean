-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:18:00.275682+00:00
-- url     : https://prove2.me/submissions/5ca6bc18-355d-4808-b2cf-7eea419edb2b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedRecentered_exists_twisted_source_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {A S : Type*} [Fintype A] (e : A → ScalarSiteExpansion S)

theorem commonSitePeriod_pos {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a)) (k : ∀ a, (e a).Term) :
    0 < commonSitePeriod e k :=
  Finset.prod_pos (fun a _ => (he a).period_pos (k a))

theorem commonSitePeriod_le_pow {T V C H : A → ℝ} {L : ℝ≥0}
    (he : ∀ a, (e a).Bounds (T a) (V a) (C a) L (H a))
    {D : ℝ} (hD : ∀ a, V a ≤ D) (k : ∀ a, (e a).Term) :
    (commonSitePeriod e k : ℝ) ≤ D ^ Fintype.card A := by
  rw [commonSitePeriod, Nat.cast_prod]
  calc
    _ ≤ ∏ _a : A, D := Finset.prod_le_prod (fun a _ => Nat.cast_nonneg _)
      (fun a _ => ((he a).period_le (k a)).trans (hD a))
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativePhysicalHaarExpansion
namespace OAI

section

namespace Erdos3
open scoped NNReal

namespace VectorPolynomial
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem physicalFactorCoverMap_lipschitz (period gridPeriod : ℕ) :
    LipschitzWith (max (max ((period * gridPeriod : ℕ) : ℝ≥0) gridPeriod) period)
      (physicalFactorCoverMap (J := J) period gridPeriod) :=
  ((torus_nsmul_reindex_lipschitz (fun a : JetAmbientIndex (fun _ : Fin m => Unit) J =>
    (⟨a.1, a.2.2⟩ : Σ j, J j)) (period * gridPeriod)).prodMk
      (torus_nsmul_reindex_lipschitz id gridPeriod)).prodMk
        (torus_nsmul_reindex_lipschitz id period)

theorem physicalFactorCoverMap_lipschitz_mul (period gridPeriod : ℕ)
    [NeZero period] [NeZero gridPeriod] :
    LipschitzWith ((period * gridPeriod : ℕ) : ℝ≥0) (physicalFactorCoverMap (J := J) period gridPeriod) := by
  have hp : (period : ℝ≥0) ≤ ((period * gridPeriod : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_mul_of_pos_right period (Nat.pos_of_neZero gridPeriod)
  have hg : (gridPeriod : ℝ≥0) ≤ ((period * gridPeriod : ℕ) : ℝ≥0) := by
    exact_mod_cast Nat.le_mul_of_pos_left gridPeriod (Nat.pos_of_neZero period)
  exact (physicalFactorCoverMap_lipschitz period gridPeriod).weaken (max_le (max_le le_rfl hg) hp)

omit [∀ j, Fintype (J j)] in
theorem physicalFactorCoverMap_input {X : Type*} (period gridPeriod : ℕ)
    [NeZero period] [NeZero gridPeriod]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    physicalFactorCoverMap period gridPeriod (physicalGridFactorInput (period * gridPeriod) p t) =
      (physicalMaskedFactorInput period p t, physicalGridFactorInput gridPeriod p t) := by
  have hp : (period : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne period)
  have hg : (gridPeriod : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne gridPeriod)
  apply Prod.ext
  · apply Prod.ext
    · funext a
      simp only [physicalFactorCoverMap, physicalGridFactorInput, physicalMaskedFactorInput,
        ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
      congr 1
      field_simp
    · funext a
      simp only [physicalFactorCoverMap, physicalGridFactorInput, physicalMaskedFactorInput,
        ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
      congr 1
      field_simp
  · funext a
    simp only [physicalFactorCoverMap, physicalGridFactorInput,
      ← AddCircle.coe_nsmul, nsmul_eq_mul, Nat.cast_mul]
    congr 1
    field_simp

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedNormalizedNativeModel
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem AllocatedModelPhysicalExpansionIdentity.exists_large_source_term
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℂ)
    (frame : Ω → X → (Unit ⊕ Fin dim) → ℤ) {δ Cmass : ℝ}
    (hδ : 0 < δ) (hCmass : 0 < Cmass)
    (hmass : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmass)
    (hpositive : δ ≤ (∑ z, weight z *
      (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)) *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)))).re) :
    ∃ label i k, δ / Cmass ≤ ‖∑ z, weight z *
      ∏ site, g label i k site
        (physicalMaskedFactorInput period p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)),
        physicalGridFactorInput (commonSitePeriod e k) p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)))‖ := by
  let coeff := fun (label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) (i : T) (k : ∀ a, (e a).Term) => ((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
    allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
    coverSiteCoefficient e k
  let value := fun label i k z => ∏ site, g label i k site
    (physicalMaskedFactorInput period p
      (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)),
    physicalGridFactorInput (commonSitePeriod e k) p
      (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)))
  have heq : (∑ z, weight z * ∑ label, ∑ i, ∑ k, coeff label i k * value label i k z) =
      ∑ label, ∑ i, ∑ k, coeff label i k * ∑ z, weight z * value label i k z := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro label _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro z _
    ring
  unfold AllocatedModelPhysicalExpansionIdentity at hidentity
  simp_rw [hidentity] at hpositive
  change δ ≤ (∑ z, weight z * ∑ label, ∑ i, ∑ k, coeff label i k * value label i k z).re at hpositive
  rw [heq] at hpositive
  obtain ⟨⟨label, i, k⟩, hterm⟩ := exists_large_weighted_term
    (fun v : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) ×
      T × (∀ a, (e a).Term) => coeff v.1 v.2.1 v.2.2)
    (fun v => ∑ z, weight z * value v.1 v.2.1 v.2.2 z) hδ hCmass
    (by simpa only [Fintype.sum_prod_type] using hmass)
    (by simpa only [Fintype.sum_prod_type] using hpositive.trans (Complex.re_le_norm _))
  exact ⟨label, i, k, hterm⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

theorem AllocatedModelPhysicalExpansionIdentity.exists_common_cover_source
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    {Ω : Type*} [Fintype Ω] (weight : Ω → ℂ)
    (frame : Ω → X → (Unit ⊕ Fin dim) → ℤ) {δ Cmass : ℝ}
    (hδ : 0 < δ) (hCmass : 0 < Cmass)
    (hmass : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmass)
    (hpositive : δ ≤ (∑ z, weight z *
      (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)) *
      allocatedFullGridChartModel B U b S rowSets d hb o bW e
        (BooleanCubeKernel.physicalCubeRowSample U d rows p hm (frame z)))).re) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
      δ / Cmass ≤ ‖∑ z, weight z * ∏ site, F site (physicalGridFactorInput cover p
        (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)))‖ := by
  obtain ⟨label, i, k, hterm⟩ := AllocatedModelPhysicalExpansionIdentity.exists_large_source_term
    B U b S x y₀ q d period r hr hb o bW e a f p hm g hidentity weight frame hδ hCmass hmass hpositive
  let cover := period * commonSitePeriod e k
  have hpos := commonSitePeriod_pos e he k
  let : NeZero (commonSitePeriod e k) := ⟨hpos.ne'⟩
  have hk : (commonSitePeriod e k : ℝ≥0) ≤
      Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by
    exact_mod_cast commonSitePeriod_le_pow e he hVmax k
  let F := fun site => g label i k site ∘ physicalFactorCoverMap period (commonSitePeriod e k)
  refine ⟨cover, Nat.mul_pos (NeZero.pos period) hpos, ?_, F, ?_, ?_, ?_⟩
  · have hkreal : (commonSitePeriod e k : ℝ) ≤
        (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} := by exact_mod_cast hk
    dsimp only [cover]
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left hkreal (Nat.cast_nonneg _)
  · intro site
    apply ((hg label i k site).comp (physicalFactorCoverMap_lipschitz_mul period (commonSitePeriod e k))).weaken
    simp only [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk zero_le) zero_le
  · intro site z
    exact hgb label i k site _
  · have hvalue (z : Ω) (site : Finset (Fin dim)) :
        F site (physicalGridFactorInput cover p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ))) =
        g label i k site (physicalMaskedFactorInput period p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ)),
          physicalGridFactorInput (commonSitePeriod e k) p
          (fun u => (BooleanCubeKernel.physicalCubeVertexValue (frame z) site u : ℝ))) :=
      congrArg (g label i k site) (physicalFactorCoverMap_input period (commonSitePeriod e k) p _)
    simpa only [hvalue] using hterm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin dim)))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable {X : Type*} [Fintype X] (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S X spatialModulus stride wholeReference x base label
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin dim)
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "terms" => (X → SpatialSiteLabel (Fin dim) spatialModulus 4 mesh)
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S X spatialModulus stride wholeReference x N mesh base label

theorem AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source_s2_oai
    (g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin dim) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z) (hmesh : 0 < mesh)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    {δ Cmodel Cspatial : ℝ} (hδ : 0 < δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmass : (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Cmodel)
    (hspatial : allocatedSpatialCoefficientCap X selection M spatialModulus mesh ≤ Cspatial)
    (hpositive : δ ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells test).re) :
    ∃ cover : ℕ, 0 < cover ∧
      (cover : ℝ) ≤ period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ∧
    ∃ F : Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ site, LipschitzWith (L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})) (F site)) ∧
      (∀ site z, ‖F site z‖ ≤ 1) ∧
    ∃ (cell : cells) (t : terms),
      allocatedSpatialExpansionCoefficient B U b S x X hM selection hx spatialModulus hW mesh
        (principalResidueLabel spatialModulus (wholeReference label)) t ≠ 0 ∧
      (∀ site u, ‖twist cell.val t site u‖ ≤ 1) ∧
      δ / (Cmodel * Cspatial) ≤ ‖(∑ v ∈ window,
        (∏ site, test site (fun u => (physicalCubeVertexValue (reconstruct cell.val v) site u : ℝ)) *
          twist cell.val t site (physicalCubeVertexValue (reconstruct cell.val v) site)) *
        ∏ site, F site (physicalGridFactorInput cover p
          (fun u => (physicalCubeVertexValue (reconstruct cell.val v) site u : ℝ)))) / ((volume : ℝ) : ℂ)‖ := by
  let weight : cells × window → ℂ := fun z => (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
    allocatedRecenteredResidueWeight (τ := τ) B U b S X spatialModulus stride wholeReference x hM selection hx
      N hW mesh base cells (physicalCubeSiteTest test) label z.1 z.2.val
  let frame : cells × window → X → (Unit ⊕ Fin dim) → ℤ := fun z => reconstruct z.1.val z.2.val
  obtain ⟨cover, hcover, hcoverBound, F, hF, hFb, hsource⟩ :=
    AllocatedModelPhysicalExpansionIdentity.exists_common_cover_source B U b S x y₀ q d period r hr hb o bW e a f p hm
      g hidentity hg hgb he Vmax hVmax weight frame hδ hCmodel hmass hpositive
  let value : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ := fun v => ∏ site, F site (physicalGridFactorInput cover p
    (fun u => (physicalCubeVertexValue v site u : ℝ)))
  have hsource' : δ / Cmodel ≤ ‖∑ acell : cells, (selectedResidueCellWeight stride cells widths acell : ℂ) *
      ∑ v ∈ window, allocatedRecenteredResidueWeight (τ := τ) B U b S X spatialModulus stride wholeReference x
        hM selection hx N hW mesh base cells (physicalCubeSiteTest test) label acell v * value (reconstruct acell.val v)‖ := by
    convert hsource using 1
    congr 1
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro acell _
    rw [Finset.mul_sum, ← Finset.sum_coe_sort window]
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [weight, frame, value]
    ring
  obtain ⟨cell, t, hct, ht, hterm⟩ := allocatedRecentered_exists_twisted_source_s2 (ξ := ξ) B U b S X spatialModulus stride
    wholeReference x N mesh base hM selection hx hW cells hstride hmesh hbudget hperiod hV hZ
    label test value (div_pos hδ hCmodel) hCspatial hspatial hsource'
  refine ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, hct, ht, ?_⟩
  simpa only [div_div, value] using hterm

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7} := @OAI.Erdos3.VectorPolynomial.AllocatedModelPhysicalExpansionIdentity.exists_twisted_common_cover_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7}
