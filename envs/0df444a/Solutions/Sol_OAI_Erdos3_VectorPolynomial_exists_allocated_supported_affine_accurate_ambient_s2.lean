-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_ambient_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:26:13.171598+00:00
-- url     : https://prove2.me/submissions/8053be10-5318-43c5-9418-5d62324cf7a2

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_global_masked_affine_ideal_approximation_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_ambient_surrogate_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineBoundedAmbient
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

include hr hperiod hM hm hR hC hchart hbudget hu₀ hmodulus in

theorem exists_allocated_supported_affine_ambient_approximation
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {ε p : ℝ} (hε : 0 < ε) (hp : 0 ≤ p)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p)
    (hεp : ε⁻¹ ≤ Real.exp p) (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp p) :
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    let mass := Real.toNNReal ((2 : ℝ) ^ Fintype.card (Finset α) * ‖inverseNormalizer‖ *
      ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) * maskCap * A))
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ +
      Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * allocatedRowSlicedSiteRadius rowSets)
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lsite := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord * d +
      max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let Lgrid := (Fintype.card gridAxes *
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, Cforward j * Fintype.card (J j))
    let N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (N * (mass * (Lgrid * d) +
        mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) F ∧
      (∀ z, ‖F z‖ ≤ (N * mass : ℝ≥0)) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          allocatedFullGridNaturalVolume B U b S rowSets * (‖inverseNormalizer‖ * maskCap * ε) := by
  intro Q A maskCap mass L Lcoord Lsite Lrows Lgrid N
  obtain ⟨k, hk, hcard, a, f, ha, hf, hLf, hs, hc, hfn, hfm, hmeas, herr⟩ :=
    exists_allocated_global_masked_affine_ideal_approximation_s2 B U b S rowSets x y₀ q d period r hr hb o bW
      hperiod hM hm hR C hC hchart hbudget center width ρ hρ hρ1 hw hε hp hbox hεp hρp
  let Mactual := ∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖(2 : ℂ) ^ Fintype.card (Finset α) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖₊
  have hmass : Mactual ≤ mass := by
    apply NNReal.coe_le_coe.mp
    apply le_trans _ (Real.le_coe_toNNReal _)
    change (Mactual : ℝ) ≤ (2 : ℝ) ^ Fintype.card (Finset α) * ‖inverseNormalizer‖ *
      ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) * maskCap * A)
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have he : (Mactual : ℝ) = (2 : ℝ) ^ Fintype.card (Finset α) *
        (∑ label : Finset α → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i‖) := by
      simp only [Mactual, NNReal.coe_sum, coe_nnnorm, norm_mul, norm_pow, h2, Finset.mul_sum]
    rw [he]
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (by ring)
  have hη : 0 ≤ ‖inverseNormalizer‖ * maskCap * ε :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg
      (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period))) hε.le
  have hjoin := principalAxisJoin_restrict grid y₀
  have herr' : ∀ y, ‖allocatedProductFullGridPrefactor B U b S rowSets d r hr x hb o bW q
      (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀))
      ideal y - allocatedProductChartIdealApproximation B U b S rowSets x
      (principalAxisJoin grid (principalAxisRestrict grid y₀) (principalAxisRestrict (fun a => ¬grid a) y₀))
      q d period r hr hb o bW a f y‖ ≤ ‖inverseNormalizer‖ * maskCap * ε := by
    simpa only [hjoin] using herr
  obtain ⟨F, hF, hFb, hFe⟩ := exists_allocated_supported_affine_ambient_surrogate_s2 B U b hR hσ S rowSets
    H step c hH hsubset q label hcell x (principalAxisRestrict grid y₀) hu₀
    (principalAxisRestrict (fun a => ¬grid a) y₀) E d hmodulus hb o bW
    period hdiv r hr C hC hchart hbudget Cforward hforward K hK T hT hTideal hsource hradius hσ1
    ρ hρ hρ1 center width hw a f hLf hf hη herr'
  simp only [hjoin] at hF hFb
  change LipschitzWith (N * (Mactual * (Lgrid * d) +
    Mactual * (Fintype.card (Finset α) * (Lsite * Lrows)))) F at hF
  change ∀ z, ‖F z‖ ≤ (N * Mactual : ℝ≥0) at hFb
  refine ⟨F, hF.weaken ?_, ?_, hFe⟩
  · gcongr
  · intro z
    exact (hFb z).trans (by exact_mod_cast mul_le_mul_of_nonneg_left hmass (show 0 ≤ N from zero_le))

include hr hperiod hM hm hR hC hchart hbudget hu₀ hmodulus in

theorem exists_allocated_supported_affine_accurate_ambient_s2_oai
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Pbox Prho Vlog Nlog Mlog target : ℝ}
    (hPbox : 0 ≤ Pbox) (hPrho : 0 ≤ Prho) (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog) (htarget : 0 ≤ target)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖inverseNormalizer‖ ≤ Real.exp Nlog)
    (hmask : M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period ≤ Real.exp Mlog) :
    let p := Pbox + Prho + Vlog + Nlog + Mlog + target
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let A := Real.exp ((Fintype.card (Finset α) * Fintype.card (LayerSamplerAxis I n) : ℕ) * (4 * Q + 8) + Q)
    let maskCap := M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period
    let mass := Real.toNNReal ((2 : ℝ) ^ Fintype.card (Finset α) * ‖inverseNormalizer‖ *
      ((Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
        Fintype.card (Finset α) * maskCap * A))
    let L : ℝ≥0 := ⟨Real.exp (Fintype.card (LayerSamplerAxis I n) + 6 * Q + 12), Real.exp_nonneg _⟩ +
      Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * allocatedRowSlicedSiteRadius rowSets)
    let Lcoord := K * ∑ j, Cforward j * Fintype.card (J j)
    let Lsite := (Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) * Lcoord * d +
      max (L * Lcoord * period) (4 * period) * (d / period : ℕ)
    let Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0)
    let Lgrid := (Fintype.card gridAxes *
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) *
        (2 * ((S.value : ℝ≥0) ^ (layerTailDegree m + 1)) ^ 2))) *
      (∑ j, Cforward j * Fintype.card (J j))
    let N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith (N * (mass * (Lgrid * d) +
        mass * (Fintype.card (Finset α) * (Lsite * Lrows)))) F ∧
      (∀ z, ‖F z‖ ≤ (N * mass : ℝ≥0)) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤
          Real.exp (-target) := by
  intro p Q A maskCap mass L Lcoord Lsite Lrows Lgrid N
  let e := Vlog + Nlog + Mlog + target
  let ε := Real.exp (-e)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hep : e ≤ p := by dsimp [e, p]; linarith
  have hεp : ε⁻¹ ≤ Real.exp p := by
    rw [show ε = Real.exp (-e) from rfl, ← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr hep
  have hbox' : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp p :=
    hbox.trans (Real.exp_le_exp.mpr (by dsimp [p]; linarith))
  have hρp' : (ρ : ℝ)⁻¹ ≤ Real.exp p :=
    hρp.trans (Real.exp_le_exp.mpr (by dsimp [p]; linarith))
  obtain ⟨F, hF, hFb, hFe⟩ := exists_allocated_supported_affine_ambient_approximation
    B U b S rowSets x y₀ q d period r hr hb o bW hperiod hM hm hR C hC hchart hbudget
    ρ center width hσ H step c hH hsubset label hcell hu₀ hmodulus hdiv
    Cforward hforward K hK T hT hTideal hsource hradius hσ1 hρ hρ1 hw
    (Real.exp_pos (-e)) hp hbox' hεp hρp'
  refine ⟨F, hF, hFb, ?_⟩
  intro y
  apply (hFe y).trans
  have hmask0 : 0 ≤ maskCap := mul_nonneg (pow_nonneg (zero_le_one.trans hM) _)
    (coefficientDeckPeriodCap_nonneg rowTypes E period)
  calc
    _ ≤ Real.exp Vlog * (Real.exp Nlog * Real.exp Mlog * ε) :=
      mul_le_mul hvolume (mul_le_mul_of_nonneg_right
        (mul_le_mul hnormalizer hmask hmask0 (Real.exp_nonneg _)) (Real.exp_nonneg _))
        (by positivity) (Real.exp_nonneg _)
    _ = _ := by
      dsimp only [ε, e]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_ambient_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.exists_allocated_supported_affine_accurate_ambient_s2_oai.{uα, u_1, u_2, u_3, u_4, u_5}
