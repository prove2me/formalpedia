-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:27:33.730985+00:00
-- url     : https://prove2.me/submissions/368b8deb-1646-4b85-ade1-d2c7e1aa2039

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceEarly_error_budget_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedSourceEarlyPrefactor_le_exp_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_good_kernel_source_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SlicedSourceAccuracy
namespace OAI

section

namespace Erdos3

theorem exp_neg_le_half_exp_neg {A B : ℝ} (hAB : B + 1 ≤ A) :
    Real.exp (-A) ≤ (1 / 2) * Real.exp (-B) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ Real.exp (-(B + 1)) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-B) / Real.exp 1 := by simp only [neg_add, Real.exp_add, Real.exp_neg, div_eq_mul_inv]
    _ ≤ Real.exp (-B) / 2 := div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h2
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

theorem slicedSourceAccuracy_bounds {Q G E : ℝ} (hQ : 0 ≤ Q) (hG : 0 ≤ G) (hE : 0 ≤ E) :
    let εgrid := Real.exp (-(Q + E + 1))
    let εlong := Real.exp (-(G + E + 1))
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Q + E + 1) ∧
    0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ = Real.exp (G + E + 1) ∧
    ∀ C : ℝ, C ≤ Real.exp G → Real.exp Q * εgrid + εlong * C ≤ Real.exp (-E) := by
  intro εgrid εlong
  have hg : εgrid ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hQ, hE])
  have hl : εlong ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hG, hE])
  refine ⟨Real.exp_pos _, hg, ?_, Real.exp_pos _, hl, ?_, ?_⟩
  · simp only [εgrid, Real.exp_neg, inv_inv]
  · simp only [εlong, Real.exp_neg, inv_inv]
  · intro C hC
    have hhalf := exp_neg_le_half_exp_neg (A := E + 1) (B := E) le_rfl
    have hgrid : Real.exp Q * εgrid = Real.exp (-(E + 1)) := by
      dsimp [εgrid]
      rw [← Real.exp_add]
      congr 1
      ring
    have hlong : εlong * Real.exp G = Real.exp (-(E + 1)) := by
      dsimp [εlong]
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.exp Q * εgrid + εlong * Real.exp G :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (Real.exp_nonneg _))
      _ = 2 * Real.exp (-(E + 1)) := by rw [hgrid, hlong]; ring
      _ ≤ Real.exp (-E) := by linarith only [hhalf]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineSourceAccuracy
namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

theorem affineSourceAccuracy_budget
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {Dout Dgrid Prho Pbox Op E F C : ℝ}
    (hDout : 0 ≤ Dout) (hDgrid : 0 ≤ Dgrid) (hPrho : 0 ≤ Prho)
    (hPbox : 0 ≤ Pbox) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hout : (Fintype.card κ : ℝ) ≤ Dout) (hgrid : (Fintype.card ι : ℝ) ≤ Dgrid)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hC0 : 0 ≤ C) (hC : C ≤ Real.exp F) :
    let G := Dgrid * max Op 0
    let εgrid := Real.exp (-(Dout * Prho + (E + F) + 1))
    let εlong := Real.exp (-(G + (E + F) + 1))
    let Plong := Pbox + Prho + G + (E + F) + 2
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Dout * Prho + (E + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp Plong ∧
      0 ≤ Plong ∧ Pbox ≤ Plong ∧ (ρ : ℝ)⁻¹ ≤ Real.exp Plong ∧
      C * ((ρ⁻¹ ^ Fintype.card κ : ℝ≥0) * εgrid +
        εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-E) := by
  intro G εgrid εlong Plong
  have hG : 0 ≤ G := mul_nonneg hDgrid (le_max_right _ _)
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, herr⟩ :=
    slicedSourceAccuracy_bounds (mul_nonneg hDout hPrho) hG (add_nonneg hE hF)
  have hPlong : G + (E + F) + 1 ≤ Plong := by dsimp [Plong]; linarith
  have hb : Pbox ≤ Plong := by dsimp [Plong]; linarith
  have hr : Prho ≤ Plong := by dsimp [Plong]; linarith
  have hcap : (ρ⁻¹ ^ Fintype.card κ : ℝ≥0) ≤ Real.exp (Dout * Prho) := by
    rw [NNReal.coe_pow, NNReal.coe_inv]
    calc
      _ ≤ (Real.exp Prho) ^ Fintype.card κ := pow_le_pow_left₀ (inv_nonneg.mpr ρ.coe_nonneg) hρ _
      _ = Real.exp (Fintype.card κ * Prho) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hout hPrho)
  have hprod : (∏ _i : ι, Real.exp Op) ≤ Real.exp G := by
    simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hgrid (le_max_right _ _))
  refine ⟨hg0, hg1, hgi, hl0, hl1, hli.trans_le (Real.exp_le_exp.mpr hPlong),
    hPbox.trans hb, hb, hρ.trans (Real.exp_le_exp.mpr hr), ?_⟩
  calc
    _ ≤ C * (Real.exp (Dout * Prho) * εgrid + εlong * ∏ _i : ι, Real.exp Op) := by
      apply mul_le_mul_of_nonneg_left _ hC0
      exact add_le_add (mul_le_mul_of_nonneg_right hcap hg0.le) le_rfl
    _ ≤ C * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_left (herr _ hprod) hC0
    _ ≤ Real.exp F * Real.exp (-(E + F)) := mul_le_mul_of_nonneg_right hC (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineSourceAccuracy
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_buffer_le_exp (rowSets : Fin m → Finset (Finset α)) :
    2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤
      Real.exp (((m : ℝ) + 2) * Fintype.card α + m + 4) := by
  let A : ℝ := ((m : ℝ) + 2) * Fintype.card α + 3
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  have hr : (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ 1 + m * idealSiteBoxRadius α m := by
    change 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1) ≤ _
    apply add_le_add_right
    calc
      _ ≤ ∑ _j : Fin m, idealSiteBoxRadius α m := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ hT
        exact_mod_cast (Finset.card_le_univ (rowSets j)).trans_eq (Fintype.card_finset (α := α))
      _ = _ := by simp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hone : 1 ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  calc
    _ ≤ 2 + m * (2 * idealSiteBoxRadius α m) := by nlinarith only [hr]
    _ ≤ 2 + m * Real.exp A := by
      gcongr
      exact idealSiteBoxRadius_buffer_le_exp α m
    _ ≤ ((m : ℝ) + 2) * Real.exp A := by nlinarith only [hone]
    _ ≤ Real.exp ((m : ℝ) + 1) * Real.exp A := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      simpa only [add_assoc, one_add_one_eq_two] using Real.add_one_le_exp ((m : ℝ) + 1)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A]; ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineAccurateSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal
attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullBooleanRowSetFintype

private theorem affineSource_sum_eq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) = affineSourceSum f := by
  unfold affineSourceSum
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_univ]
  · intro i hi
    rfl

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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

include hR hC hchart hbudget in

theorem exists_allocated_supported_affine_accurate_source_s2_oai
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
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg) (hvg : 0 ≤ vg) (hwg : 0 ≤ wg) (htg : 0 ≤ tg) (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin dim) : ℝ) ≤ Dg) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin dim) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg) (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg) (haxes : (Fintype.card gridAxes : ℝ) ≤ Dg)
    (hσgrid : ∀ j, σ j ≤ 1)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) (hTideal : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin dim) (j.val + 1)).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Prho : ℝ} (hPrho : 0 ≤ Prho) (hρPrho : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    {Pnum Pk target : ℝ} (hPnum : 0 ≤ Pnum) (hPk : 0 ≤ Pk) (htarget : 0 ≤ target)
    {Mk : ℕ} (hMk : 0 < Mk) (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum) :
    let F := (m * (2 : ℝ) ^ Fintype.card (Fin dim)) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * ((m + 1 : ℕ) * Pk))
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ)
    let Dgrid := (Fintype.card (LayerSamplerAxis I n) : ℝ)
    let Pbox := ((m : ℝ) + 2) * Fintype.card (Fin dim) + m + 4
    let Eg := Dout * Prho + (target + F) + 1
    let _εgrid := Real.exp (-Eg)
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (boundedBooleanJetRows (Fin dim) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) ((j.val + 1) * (boundedBooleanJetRows (Fin dim) (j.val + 1)).card) Dg p e
    let Cp := ∑ j, (L j 0 + Dg * (vg + 1))
    let Eg' := uniformProductAccuracyLog Dg Cp Eg + Dg * (vg + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset (Fin dim))) (L j Eg') + (Dg + 1) * (vg + 1))
    let Gcost := Dgrid * max Op 0
    let ε := Real.exp (-(Gcost + (target + F) + 1))
    let Plong := Pbox + Prho + Gcost + (target + F) + 2
    ∃ e : gridAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim)),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog Dg vg wg tg + (Dg + vg + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (selection : Fin dim ↪ G)
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
        (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin dim)) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤
          Real.exp (2 * Fintype.card (Finset (Fin dim)) + F +
            Fintype.card (Finset (Fin dim)) * ((∑ j, Fintype.card (J j) : ℕ) * ((m + 1 : ℕ) * Pk)) +
            ((Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q) +
            Fintype.card gridAxes * Op) ∧
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
            Real.exp (-target)) ∧
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
  intro F Dout Dgrid Pbox Eg εgrid p L Cp E' Op Gcost ε Plong
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _))
          (add_nonneg hPnum (by norm_num)))
          (add_nonneg zero_le_one (mul_nonneg (by norm_num) hPnum)))
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hPk)))
      (Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hPk))))
  have hEg : 0 ≤ Eg := add_nonneg
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hPrho) (add_nonneg htarget hF)) zero_le_one
  have hPper : 0 ≤ (m + 1 : ℕ) * Pk := mul_nonneg (Nat.cast_nonneg _) hPk
  have hPbox : 0 ≤ Pbox := add_nonneg
    (add_nonneg (mul_nonneg (add_nonneg (Nat.cast_nonneg _) zero_le_two) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)) (by norm_num)
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, hp, hbp, hrp, _⟩ :=
    affineSourceAccuracy_budget (ι := Empty) (κ := Empty)
      (Dout := Dout) (Dgrid := Dgrid) (Pbox := Pbox) (Op := Op)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hPrho hPbox htarget hF
      (by simp only [Fintype.card_ofIsEmpty, Nat.cast_zero]; exact Nat.cast_nonneg _)
      (by simp only [Fintype.card_ofIsEmpty, Nat.cast_zero]; exact Nat.cast_nonneg _)
      ρ hρPrho (C := 0) le_rfl (Real.exp_nonneg _)
  have hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Plong :=
    (allocatedRowSlicedSiteRadius_buffer_le_exp rowSets).trans (Real.exp_le_exp.mpr hbp)
  obtain ⟨e, heb, he⟩ := exists_allocated_supported_affine_good_kernel_source_s2
    B U b S q r hr hb o bW hR C hC hchart hbudget ρ center width hσ H step c hH hsubset label hcell
    Cforward hforward K hK Qgrid hQgrid hdim hq hδg hdenseg Tg hQTg hstep Ag hAg Pg hPg hcP hsP
    hstride hBa hBi hDg hvg hwg htg hpg hEg hcube hdegree hrowsD htail hblocks hRv hRi hδw hTg
    hcoeff hPp₀ haxes hg0 hgi.le hσgrid T hT hTideal hsource hradius hσ1
    hρ hρ1 hw hl0 hp hbox hli hrp
  refine ⟨e, ?_, ?_⟩
  · simpa only [Op, E', Cp, L, p, Fintype.card_eq_nat_card] using heb
  intro x selection hx
  obtain ⟨candidate, hcanonical, hspatial, hsourceModel⟩ := he x hMk selection hx
  refine ⟨candidate, hcanonical, hspatial, ?_⟩
  intro y₀ d hd hdiv hqperiod hu₀ hy₀
  let period := kernelPeriodCandidate (m + 1) candidate
  intro sourceRadius cutoffLip Q A maskCap
  obtain ⟨k, hk, hcard, a₀, f, ha₀, hf, hLf, hs, hc, hfn, hfm, hmeas, hlong, herr, hphysical⟩ :=
    hsourceModel y₀ d hdiv hqperiod hu₀ hy₀
  obtain ⟨_, _, _, _, _, _, _, _, _, herror⟩ :=
    allocatedAffineSourceEarly_error_budget_s2 B U b S rowSets E hR hPnum hI hn hcoeffEarly hRiEarly hVEarly
      (Op := Op) hPk hPper hPrho htarget hMkPk
      (kernelPeriodCandidate_le_exp hMkPk (m + 1) candidate) ρ hρPrho
  have hpref := allocatedSlicedSourceEarlyPrefactor_le_exp_s2 B U b S rowSets E hR
    hPnum hI hn hcoeffEarly hRiEarly hVEarly hMkPk
    (kernelPeriodCandidate_le_exp hMkPk (m + 1) candidate)
  have hmass := allocatedFiniteModelPhysicalCoefficientMass_le_exp_s2 B U b S x y₀ q d period
    hb bW e a₀ (F := F)
    (A := (Fintype.card (Finset (Fin dim)) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    (Op := Op) (Nat.cast_nonneg (layerKernelIndexBound m Mk))
    (by simpa only [F, period, coefficientDeckPeriodCap, Fintype.card_eq_nat_card] using hpref)
    (kernelPeriodCandidate_le_exp hMkPk (m + 1) candidate)
    (by simpa only [Q, coefficientDeckPeriodCap, Fintype.card_eq_nat_card] using hc)
    (by simpa only [Op, E', Cp, L, p, Fintype.card_eq_nat_card] using heb)
  refine ⟨k, ?_, ?_, a₀, f, ?_, hf, ?_, ?_, ?_, ?_, hfn, hfm, hmeas, ?_, ?_, ?_⟩
  · simpa only [Q, Fintype.card_eq_nat_card] using hk
  · simpa only [Q, Fintype.card_eq_nat_card] using hcard
  · simpa only [A, Q, Fintype.card_eq_nat_card] using ha₀
  · simpa only [cutoffLip, sourceRadius, Q, Fintype.card_eq_nat_card] using hLf
  · simpa only [sourceRadius] using hs
  · simpa only [maskCap, A, Q, coefficientDeckPeriodCap, Fintype.card_eq_nat_card] using hc
  · simpa only [affineSource_sum_eq, Fintype.card_eq_nat_card] using hmass
  · simpa only [maskCap, coefficientDeckPeriodCap, Fintype.card_eq_nat_card] using hlong
  · intro y
    apply (herr y).trans
    simpa only [F, Dout, Dgrid, Pbox, Eg, εgrid, p, L, Cp, E', Op, Gcost, ε, Plong,
      coefficientDeckPeriodCap, Fintype.card_eq_nat_card] using herror
  · intro X poly hpoly hmem
    simpa only [cutoffLip, sourceRadius, Q, Plong, Gcost, Op, E', Cp, L, p,
      Fintype.card_eq_nat_card] using
      hphysical poly hpoly hmem

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_source_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
