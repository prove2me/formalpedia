-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_good_kernel_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T03:04:44.086514+00:00
-- url     : https://prove2.me/submissions/3457b916-370b-41f1-88a5-c0ff0795d98b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B198
import Definitions.Def_OAIErdos3B1374
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_uniform_physical_source

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineAccurateSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal







end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal









end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal









end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uα

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal








end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype








end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) (Fin.val j + 1)})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := (Fin dim)) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := (Fin dim)) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

include hR hC hchart hbudget in

theorem exists_allocated_supported_affine_good_kernel_source_oai
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (Qgrid : ℝ≥0) (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤ Qgrid)
    (hdim : dim ≤ m + 1)
    (hq : 0 < q) {δg : ℝ} (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U b S tg ≤ (H tg : ℝ))
    (Tg : ℕ) (hQTg : (((Fintype.card (Fin dim) + 1) * q : ℕ) : ℝ) / δg ≤ Tg)
    (hstep : ∀ tg, 0 < step tg)
    (Ag : ℝ≥0) (hAg : LipschitzWith Ag Real.smoothTransition) (Pg : ℝ) (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) Ag 1 0 q ≤ Pg)
    (hstride : ∀ tg, ((step tg * q : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg Eg εgrid : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg) (hEg : 0 ≤ Eg)
    (hcube : (Fintype.card (Fin dim) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hεgrid : 0 < εgrid) (hεgridEg : εgrid⁻¹ ≤ Real.exp Eg) (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (hTideal : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin dim) (j.val + 1)).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε Plong : ℝ} (hε : 0 < ε) (hPlong : 0 ≤ Plong)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Plong)
    (hεp : ε⁻¹ ≤ Real.exp Plong) (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Plong) :
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j Eg') + (Dg + 1) * (vg + 1))
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        {Mk : ℕ} (_hMk : 0 < Mk) (selection : Fin dim ↪ G)
        (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x),
      ∃ candidate : Fin Mk, candidate = goodKernelUniformCandidate selection x hx m ∧
        let period := kernelPeriodCandidate (m + 1) candidate
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (period : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        ∀ (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
          (d : ℕ) [NeZero d] (_hdiv : period ∣ d) (_hqperiod : period ∣ q)
        (_hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
          (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
          (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
        (_hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ))),
    let sourceRadius : ℝ≥0 := allocatedRowSlicedSiteRadius rowSets
    let cutoffLip : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * sourceRadius)
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) Plong
    let A := Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    ∃ k : ℕ, (k : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      (Fintype.card (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) : ℝ) ≤
        Real.exp ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8)) ∧
      ∃ (a : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → Finset (Fin dim) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ i, ‖a i‖) ≤ A ∧
        (∀ i s v, ‖f i s v‖ ≤ 1) ∧
        (∀ i s, LipschitzWith (⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) (f i s)) ∧
        (∀ i s v, (∃ j, 2 * (sourceRadius : ℝ) < |v j|) → f i s v = 0) ∧
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i,
          ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) ≤
          ‖inverseNormalizer‖ * ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^ Fintype.card (Finset (Fin dim)) * maskCap * A) ∧
        (∀ label i s y,
          ‖allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s) y‖ ≤ 1) ∧
        (∀ label i s, Measurable (allocatedMaskedSiteChartFactor B U b S o hb bW d r hr period label (f i s))) ∧
        Measurable (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q y₀
              (allocatedRowSlicedIdeal B U b S rowSets ρ center width) y -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y‖ ≤
            ‖inverseNormalizer‖ * maskCap * ε) ∧
        (∀ y : EuclideanJetLayers U rowTypes,
          ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
              (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
            allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f y *
              allocatedFullGridChartModel B U b S rowSets d hb o bW e y‖ ≤
            ‖inverseNormalizer‖ * maskCap *
              ((ρ⁻¹ ^ Fintype.card (Σ a : {a // ¬grid a}, rowTypes a.val.1) : ℝ≥0) * εgrid +
                ε * ∏ _a : gridAxes, Real.exp Op)) ∧
        ∀ {X : Type*} (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
          (hm : ∀ j e, coefficients (poly j) e ∈ U j),
          let Lcoord : ℝ≥0 := K * ∑ j, Cforward j * Fintype.card (J j)
          let Llong : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord +
            max ((⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ + cutoffLip) * Lcoord * (Mk ^ (m + 1) : ℝ≥0)) (4 * (Mk ^ (m + 1) : ℝ≥0))
          let Lprimitive : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg Op⟩
          let Lgrid : ℝ≥0 := max ((((Fintype.card gridAxes : ℝ≥0) * Lprimitive) * Qgrid) *
            Lcoord * Lprimitive ^ Fintype.card gridAxes) (4 * Lprimitive ^ Fintype.card gridAxes)
          ∃ g : (Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
              (Finset (Fin dim) × LayerSamplerAxis I n → Fin k) → (∀ a, (e a).Term) → Finset (Fin dim) →
              (((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle)) ×
                ((Σ j, J j) → UnitAddCircle)) → ℂ,
            (∀ label i kg t, LipschitzWith (Llong + Lgrid) (g label i kg t)) ∧
            (∀ label i kg t z, ‖g label i kg t z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f poly hm g := by
  intro p L Cp E' Op
  obtain ⟨e, heb, he⟩ := exists_allocated_supported_affine_uniform_physical_source
    B U b S q r hr hb o bW hR C hC hchart hbudget ρ center width hσ H step c hH hsubset label hcell
    Cforward hforward K hK Qgrid hQgrid hq hδg hdenseg Tg hQTg hstep Ag hAg Pg hPg hcP hsP
    hstride hBa hBi hDg hvg hwg htg hpg hEg hcube hdegree hrowsD htail hblocks hRv hRi hδw hTg
    hcoeff hPp₀ haxes hεgrid hεgridEg hσgrid T hT hTideal hsource hradius hσ1
    hρ hρ1 hw hε hPlong hbox hεp hρp
  refine ⟨e, heb, ?_⟩
  intro x Mk hMk selection hx
  let candidate := goodKernelUniformCandidate selection x hx m
  obtain ⟨hspatial, hperiodAll⟩ := goodKernelUniformCandidate_spec selection x hx m
  refine ⟨candidate, rfl, hspatial, ?_⟩
  intro y₀ d hd hdiv hqperiod hu₀ hy₀
  let period := kernelPeriodCandidate (m + 1) candidate
  have hperiod (j : Fin m) : integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : rowTypes j → Finset (Fin dim))).mulVecLin.range :=
    @hperiodAll (rowTypes j) (Subtype.fintype _) (j.val + 1) (by omega) _ Subtype.val_injective
      (fun t => (mem_boundedBooleanJetRows (j.val + 1) t.val).mp t.property)
  have hM : (1 : ℝ) ≤ (layerKernelIndexBound m Mk : ℝ) := by
    exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1 ≤ Mk))
  have hmask := fun j z => allocatedIntegerKernelMask_bound B U b S x rows hMk selection hx
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective)
    (fun j t => (mem_boundedBooleanJetRows (j.val + 1) t.val).mp t.property) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q) z
  have hqimage := fun j => (@integerScalarLattice_le_of_nat_dvd (rowTypes j) (Subtype.fintype _)
    period q hqperiod).trans (hperiod j)
  obtain ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr, hphysical⟩ :=
    he x y₀ d period hdiv hperiod hM hmask hu₀ hqimage hy₀
  refine ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr, ?_⟩
  intro X poly hp hm Lcoord Llong Lprimitive Lgrid
  obtain ⟨g, hg, hgb, hidentity⟩ := hphysical poly hp hm
  refine ⟨g, ?_, hgb, hidentity⟩
  intro label i kg t
  apply (hg label i kg t).weaken
  have hper : (period : ℝ≥0) ≤ (Mk ^ (m + 1) : ℝ≥0) := by
    exact_mod_cast kernelPeriodCandidate_le (m + 1) candidate
  apply add_le_add _ le_rfl
  exact add_le_add le_rfl (max_le_max (mul_le_mul_of_nonneg_left hper zero_le)
    (mul_le_mul_of_nonneg_left hper zero_le))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype









end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_good_kernel_source_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_good_kernel_source_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
