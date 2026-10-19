-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSlicedSourceEarlyPrefactor_le_exp_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:06:17.139995+00:00
-- url     : https://prove2.me/submissions/acb845ab-5a4f-4f78-abf9-6fc8def5a363

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B216

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedRefinedLongJetComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)

omit [∀ j, DecidableEq (O j)] in
theorem allocatedLongJetOutputScale_pos (a : {a // ¬grid a}) :
    0 < allocatedLongJetOutputScale B U basis S (O := O) a := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  cases a with
  | inl i => exact zero_lt_one
  | inr i => exact pow_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)) _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hR in
theorem allocatedPrincipalGridScale_pos_of_radius : 0 < scale := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (principalProfileSize_pos (hR j) _)
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))

include hR in
theorem allocatedPrincipalChartRatio_pos :
    0 < allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i := by
  exact div_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i))

include hR in
theorem allocatedPrincipalChartRatio_le :
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i ≤
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) / R j := by
  have hN : (0 : ℝ) < scale :=
    Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i)
  have hg : 0 < gamma := principalProfileSize_pos (hR j) _
  have hlow : gamma * (basisAxisScale (basis j) i : ℝ) ≤ scale := Nat.le_ceil _
  calc
    _ ≤ 1 / gamma := (div_le_div_iff₀ hN hg).mpr (by nlinarith)
    _ = _ := by
      unfold principalProfileSize
      field_simp

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedProbabilityGrid
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem allocatedGridAxisScale_bounds (a : {a // grid a}) :
    1 ≤ allocatedGridAxisScale B U b S a ∧
      allocatedGridAxisScale B U b S a ≤ (S.value : ℝ≥0) ^ (layerTailDegree m + 1) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · constructor
    · change (1 : ℝ≥0) ≤ (basisAxisScale (b j) i : ℝ≥0)
      exact_mod_cast Nat.succ_le_of_lt (basisAxisScale_pos (b j) i)
    · change (basisAxisScale (b j) i : ℝ≥0) ≤ _
      change basisAxisScale (b j) i ≤ S.value ^ (layerTailDegree m + 1) at ha
      exact_mod_cast ha

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedErrorInterpolation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

theorem allocatedGridJetScale_pos : 0 < allocatedGridJetScale B U b S (O := O) :=
  Finset.prod_pos (fun a _ => pow_pos
    (lt_of_lt_of_le zero_lt_one (by exact_mod_cast (allocatedGridAxisScale_bounds B U b S a).1)) _)

theorem allocatedGridLongJetScale_product :
    allocatedGridJetScale B U b S (O := O) * longScale =
      ∏ j, (∏ i, (basisAxisScale (b j) i : ℝ)) ^ Fintype.card (O j) := by
  let f : LayerSamplerAxis I n → ℝ := fun a =>
    match a with
    | ⟨_, .inl _⟩ => 1
    | ⟨j, .inr i⟩ => (basisAxisScale (b j) i : ℝ) ^ Fintype.card (O j)
  have hg : (∏ a : {a // grid a}, f a.val) = allocatedGridJetScale B U b S (O := O) := by
    apply Finset.prod_congr rfl
    intro a _
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · rfl
  have hl : (∏ a : {a // ¬grid a}, f a.val) = longScale := by
    apply Finset.prod_congr rfl
    intro a _
    rcases a with ⟨⟨j, i | i⟩, ha⟩ <;> rfl
  rw [← hg, ← hl, Fintype.prod_subtype_mul_prod_subtype]
  change (∏ a : Σ j, I j ⊕ Fin (n j), f a) = _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fintype.prod_sum_type]
  simp only [f, Finset.prod_const_one, one_mul, Finset.prod_pow]

theorem allocatedGridLongJetScale_covolume :
    (allocatedGridJetScale B U b S (O := O) * longScale * coveredJetArrayScale (O := O) U)⁻¹ =
      ∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j) := by
  rw [allocatedGridLongJetScale_product, coveredJetArrayScale, ← Finset.prod_mul_distrib,
    ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← mul_pow, ← inv_pow, mul_inv_rev, inv_inv, mixedDensityCovolumeRatio, div_eq_mul_inv]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

local notation "ig" => allocatedGridIntegerAxis B U b S

local notation "axisN" => allocatedGridNaturalScale B U b S

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridNaturalScale_pos (a : gridAxes) : 0 < axisN a :=
  allocatedPrincipalGridScale_pos_of_radius B U b hR (ig a).1 (ig a).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_pos : 0 < allocatedFullGridNaturalVolume B U b S rowSets :=
  Finset.prod_pos (fun a _ => pow_pos (Nat.cast_pos.mpr (allocatedGridNaturalScale_pos B U b hR S a)) _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalNormalizer
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "naturalVolume" => allocatedFullGridNaturalVolume B U b S rowSets
local notation "gridScale" => allocatedGridJetScale B U b S (O := rowTypes)
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)
local notation "radiusVolume" => (∏ t : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))), R (Sigma.fst (Subtype.val (Sigma.fst t))))

omit [Fintype α] [DecidableEq α] in
theorem allocatedGridJetScale_natural_ratio :
    gridScale / naturalVolume = ∏ a : {a // grid a},
      (allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2) ^
        Fintype.card (rowTypes a.val.1) := by
  unfold allocatedGridJetScale allocatedFullGridNaturalVolume
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · simp only [allocatedGridAxisScale, allocatedGridNaturalScale, allocatedGridIntegerAxis,
      allocatedPrincipalChartRatio, Fintype.card_coe, div_pow, NNReal.coe_natCast]
    norm_cast

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hR : ∀ j, 0 < R j)

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_pos :
    0 < allocatedProductIdealNormalizer B U b S rowSets := by
  exact mul_pos (mul_pos (mul_pos (allocatedFullGridNaturalVolume_pos B U b hR S rowSets)
    (coveredJetArrayScale_pos U))
    (Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)))
    (Finset.prod_pos (fun t _ => hR (Sigma.fst (Subtype.val (Sigma.fst t)))))

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_eq :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (rowTypes j)) *
      (∏ a : {a // grid a},
        allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
          Fintype.card (rowTypes a.val.1)) * radiusVolume⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg
    (allocatedProductIdealNormalizer_pos B U b S rowSets hR).le]
  rw [← allocatedGridJetScale_natural_ratio B U b S rowSets,
    ← allocatedGridLongJetScale_covolume B U b S (O := rowTypes)]
  have hg := (allocatedGridJetScale_pos B U b S (O := rowTypes)).ne'
  have hn := (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).ne'
  have hl : longScale ≠ 0 := (Finset.prod_pos
    (fun a _ => allocatedLongJetOutputScale_pos B U b S a)).ne'
  have hc := (coveredJetArrayScale_pos (O := rowTypes) U).ne'
  have hr : radiusVolume ≠ 0 := (Finset.prod_pos (fun t _ => hR (Sigma.fst (Subtype.val (Sigma.fst t))))).ne'
  unfold allocatedProductIdealNormalizer
  field_simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "radiusVolume" => (∏ t : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))), R (Sigma.fst (Subtype.val (Sigma.fst t))))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hR : ∀ j, 0 < R j)

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_le (V : Fin m → ℝ)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {Q κ : ℝ} (hQ : 1 ≤ Q) (hκ0 : 0 ≤ κ) (hκ : ∀ j, (R j)⁻¹ ≤ κ)
    (hslots : ∀ j i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Q) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      (∏ j, V j ^ Fintype.card (rowTypes j)) *
        (Q * κ) ^ Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) := by
  have hV0 (j) : 0 ≤ V j := (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le.trans (hV j)
  have hbase : 0 ≤ Q * κ := mul_nonneg (zero_le_one.trans hQ) hκ0
  have hg0 : 0 ≤ ∏ a : {a // grid a},
      allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
        Fintype.card (rowTypes a.val.1) :=
    Finset.prod_nonneg (fun a _ => pow_nonneg (allocatedPrincipalChartRatio_pos B U b hR _ _).le _)
  have hl0 : 0 ≤ radiusVolume⁻¹ := inv_nonneg.mpr (Finset.prod_nonneg (fun t _ => (hR (Sigma.fst (Subtype.val (Sigma.fst t)))).le))
  have hgrid : (∏ a : {a // grid a},
      allocatedPrincipalChartRatio (G := G) B U b (R := R) (ig a).1 (ig a).2 ^
        Fintype.card (rowTypes a.val.1)) ≤
      ∏ a : {a // grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1) := by
    apply Finset.prod_le_prod
    · intro a _
      exact pow_nonneg (allocatedPrincipalChartRatio_pos B U b hR _ _).le _
    · intro a _
      apply pow_le_pow_left₀ (allocatedPrincipalChartRatio_pos B U b hR _ _).le
      apply (allocatedPrincipalChartRatio_le B U b hR _ _).trans
      rw [div_eq_mul_inv]
      exact mul_le_mul (hslots _ _) (hκ _) (inv_nonneg.mpr (hR _).le) (zero_le_one.trans hQ)
  have hlong : radiusVolume⁻¹ ≤
      ∏ a : {a // ¬grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1) := by
    simp only [Fintype.prod_sigma, Finset.prod_const, Finset.card_univ, ← Finset.prod_inv_distrib, ← inv_pow]
    apply Finset.prod_le_prod
    · intro a _
      exact pow_nonneg (inv_nonneg.mpr (hR a.val.1).le) _
    · intro a _
      apply pow_le_pow_left₀ (inv_nonneg.mpr (hR a.val.1).le)
      exact (hκ a.val.1).trans (le_mul_of_one_le_left hκ0 hQ)
  have hcov : (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^
      Fintype.card (rowTypes j)) ≤ ∏ j, V j ^ Fintype.card (rowTypes j) := by
    apply Finset.prod_le_prod
    · intro j _
      exact pow_nonneg (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le _
    · intro j _
      exact pow_le_pow_left₀ (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le (hV j) _
  rw [allocatedProductIdealNormalizer_inv_eq B U b S rowSets hR, mul_assoc]
  calc
    _ ≤ (∏ j, V j ^ Fintype.card (rowTypes j)) *
        ((∏ a : {a // grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1)) *
          ∏ a : {a // ¬grid a}, (Q * κ) ^ Fintype.card (rowTypes a.val.1)) :=
      mul_le_mul hcov
        (mul_le_mul hgrid hlong hl0 (Finset.prod_nonneg (fun a _ => pow_nonneg hbase _)))
        (mul_nonneg hg0 hl0) (Finset.prod_nonneg (fun j _ => pow_nonneg (hV0 j) _))
    _ = _ := by
      rw [Fintype.prod_subtype_mul_prod_subtype grid
        (fun a : LayerSamplerAxis I n => (Q * κ) ^ Fintype.card (rowTypes a.1)),
        Finset.prod_pow_eq_pow_sum, Fintype.card_sigma]

omit [Fintype α] [DecidableEq α] in
include hR in
theorem allocatedProductIdealNormalizer_inv_le_exp {P : ℝ} (hP : 0 ≤ P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P)
    (hκ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hslots : ∀ j i, 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp (((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) * P +
        (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) * (2 * P)) := by
  have h := allocatedProductIdealNormalizer_inv_le B U b S rowSets hR (fun _ => Real.exp P) hV
    (Real.one_le_exp hP) (Real.exp_pos P).le hκ hslots
  apply h.trans_eq
  simp only [← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedCanonicalBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem coefficientDeckPeriodCap_le_exp {m : ℕ} (O E : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (E j)] (period : ℕ) {P : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp P) :
    coefficientDeckPeriodCap O E period ≤
      Real.exp (∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (O j) * P)) := by
  have hrow (j : Fin m) : (period : ℝ) ^ Fintype.card (O j) ≤
      Real.exp (Fintype.card (O j) * P) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
  calc
    _ ≤ ∏ j, ∏ _i : E j, Real.exp (Fintype.card (O j) * P) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Finset.prod_nonneg (fun _ _ => by positivity)
      · intro j _
        exact Finset.prod_le_prod (fun _ _ => by positivity) (fun _ _ => hrow j)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← Real.exp_sum]

theorem slicedSourcePrefactor_le_exp {m : ℕ} (O E : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (E j)] (period axes : ℕ)
    {C M N W P : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ Real.exp N)
    (hM0 : 0 ≤ M) (hM : M ≤ Real.exp W) (hperiod : (period : ℝ) ≤ Real.exp P) :
    C * (M ^ axes * coefficientDeckPeriodCap O E period) ≤
      Real.exp (N + axes * W + ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (O j) * P)) := by
  have hMp : M ^ axes ≤ Real.exp (axes * W) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hM0 hM _
  calc
    _ ≤ Real.exp N * (Real.exp (axes * W) *
        Real.exp (∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (O j) * P))) :=
      mul_le_mul hC
        (mul_le_mul hMp (coefficientDeckPeriodCap_le_exp O E period hperiod)
          (coefficientDeckPeriodCap_nonneg O E period) (Real.exp_nonneg _))
        (mul_nonneg (pow_nonneg hM0 _) (coefficientDeckPeriodCap_nonneg O E period)) (hC0.trans hC)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, add_assoc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

omit [DecidableEq α] in
theorem allocatedIdealNormalizer_row_counts {P : ℝ} (hP : 0 ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P) :
    ((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) ≤ m * (2 : ℝ) ^ Fintype.card α ∧
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) ≤
        (m * (2 : ℝ) ^ Fintype.card α) * (2 * P) := by
  have hrow (j : Fin m) : (Fintype.card (rowTypes j) : ℝ) ≤ (2 : ℝ) ^ Fintype.card α := by
    have h := Finset.card_le_univ (rowSets j)
    rw [Fintype.card_finset] at h
    rw [Fintype.card_coe]
    exact_mod_cast h
  constructor
  · push_cast
    calc
      _ ≤ ∑ _j : Fin m, (2 : ℝ) ^ Fintype.card α := Finset.sum_le_sum (fun j _ => hrow j)
      _ = _ := by simp
  · have hcount : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) =
        ∑ j, ((Fintype.card (I j) : ℝ) + n j) * Fintype.card (rowTypes j) := by
      simp only [Fintype.card_sigma, Fintype.sum_sigma, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (∑ _a : I j ⊕ Fin (n j), (Fintype.card (rowTypes j) : ℝ)) = _
      simp
    rw [hcount]
    calc
      _ ≤ ∑ _j : Fin m, (2 * P) * (2 : ℝ) ^ Fintype.card α := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul (by linarith [hI j, hn j]) (hrow j) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by simp; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [DecidableEq α] in
theorem allocatedProductIdealNormalizer_early_budget
    (hR : ∀ j, 0 < R j) {P : ℝ} (hP0 : 0 ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (P + 8) * (1 + 4 * P)) := by
  have hP8 : 0 ≤ P + 8 := by linarith [hP0]
  have hP : P ≤ P + 8 := by linarith
  have hslots (j : Fin m) (i : Fin (n j)) :
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Real.exp (P + 8) := by
    have hc : (Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) ≤ P :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcoeff j)
    have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ 8 * (P + 1) := by linarith
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul h8 (Real.add_one_le_exp P)
        (by linarith [hP0]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h := allocatedProductIdealNormalizer_inv_le_exp B U b S rowSets hR hP8
    (fun j => (hV j).trans (Real.exp_le_exp.mpr hP))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hP)) hslots
  have hc := allocatedIdealNormalizer_row_counts (I := I) (n := n) rowSets
    hP0 hI hn
  apply h.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ (m * (2 : ℝ) ^ Fintype.card α) * (P + 8) +
        ((m * (2 : ℝ) ^ Fintype.card α) * (2 * P)) * (2 * (P + 8)) :=
      add_le_add (mul_le_mul_of_nonneg_right hc.1 hP8)
        (mul_le_mul_of_nonneg_right hc.2 (by positivity))
    _ = _ := by ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
variable (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
variable (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)

include hR hPnum hI hn hcoeff hRi hV

omit [DecidableEq α] in
theorem allocatedSlicedSourceEarlyPrefactor_le_exp_s2_oai
    {Mk period : ℕ} {Pk Pper : ℝ}
    (hMk : (Mk : ℝ) ≤ Real.exp Pk) (hperiod : (period : ℝ) ≤ Real.exp Pper) :
    ‖inverseNormalizer‖ * ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap rowTypes E period) ≤
    Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)) := by
  exact slicedSourcePrefactor_le_exp rowTypes E period (Fintype.card (LayerSamplerAxis I n))
    (norm_nonneg _) (allocatedProductIdealNormalizer_early_budget B U b S rowSets hR hPnum hI hn hcoeff hRi hV)
    (Nat.cast_nonneg _) (layerKernelIndexBound_le_exp m hMk) hperiod

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSlicedSourceEarlyPrefactor_le_exp_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.allocatedSlicedSourceEarlyPrefactor_le_exp_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
