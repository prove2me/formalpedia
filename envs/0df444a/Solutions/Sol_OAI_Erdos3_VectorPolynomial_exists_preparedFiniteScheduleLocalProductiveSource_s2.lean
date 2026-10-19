-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleLocalProductiveSource_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T08:22:37.548636+00:00
-- url     : https://prove2.me/submissions/e91b38d0-04fb-4b8d-9b73-0304a8eeea37

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B285
import Definitions.Def_OAIE3v2B290
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_preparedUniformDegreeComparison_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteScheduleDegreeGeometryModel_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedFiniteScheduleGeometryDirectSource_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeDirectSource_of_geometry_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeModelChain_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_preparedUniformDegreeProductiveSource_s2
import Theorems.Thm_OAI_Erdos3_slicedDetection_kernel_cutoff_bound_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ShortIntegerCubeBudget
namespace OAI

section

namespace Erdos3

theorem natFinsetSup_cast_le {I : Type*} (s : Finset I) (f : I → ℕ)
    {P : ℝ} (hP : 0 ≤ P) (hf : ∀ i ∈ s, (f i : ℝ) ≤ P) :
    ((s.sup f : ℕ) : ℝ) ≤ P := by
  apply (Nat.le_floor_iff hP).mp
  exact Finset.sup_le_iff.mpr (fun i hi => (Nat.le_floor_iff hP).mpr (hf i hi))

theorem integerPolynomialInitialScale_exp_bound {ε P Q : ℝ}
    (hε : 0 < ε) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hεQ : ε⁻¹ ≤ Real.exp Q) :
    (integerPolynomialInitialScale ε : ℝ) ≤ Real.exp (P+Q+17) := by
  have h8 : (8 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hx : 8 * (probabilityProfileLipschitz : ℝ) / ε ≤ Real.exp (P+Q+16) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 16 * Real.exp P * Real.exp Q := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hc := natCeil_le_exp_succ (by positivity) (by positivity) hx
  rw [show P+Q+16+1 = P+Q+17 by ring] at hc
  simp only [integerPolynomialInitialScale, Nat.cast_max, Nat.cast_one]
  exact max_le (Real.one_le_exp (by positivity)) hc

theorem principalSamplingGapRatio_exp_bound {γ P Q : ℝ}
    (hγ : 0 < γ) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hγQ : γ⁻¹ ≤ Real.exp Q) :
    (principalSamplingGapRatio γ : ℝ) ≤ Real.exp (P+Q+17) := by
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hx : 16 * (probabilityProfileLipschitz : ℝ) / γ ≤ Real.exp (P+Q+16) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 16 * Real.exp P * Real.exp Q := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hmax := max_le (Real.one_le_exp (by positivity : 0 ≤ P+Q+16)) hx
  have hc := natCeil_le_exp_succ (le_trans zero_le_one (le_max_left _ _))
    (by positivity) hmax
  simpa only [principalSamplingGapRatio, show P+Q+16+1 = P+Q+17 by ring] using hc

theorem commonPolynomialGapRatio_exp_bound {I : Type*} [Fintype I]
    (γ : I → ℝ) {P Q : ℝ} (hγ : ∀ i, 0 < γ i) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hγQ : ∀ i, (γ i)⁻¹ ≤ Real.exp Q) :
    (commonPolynomialGapRatio γ : ℝ) ≤ Real.exp (P+Q+17) := by
  simp only [commonPolynomialGapRatio, Nat.cast_max, Nat.cast_one]
  refine max_le (Real.one_le_exp (by positivity)) ?_
  apply natFinsetSup_cast_le _ _ (Real.exp_nonneg _)
  exact fun i _ => principalSamplingGapRatio_exp_bound (hγ i) hP hQ hA (hγQ i)

theorem commonPolynomialInitialScale_exp_bound {I : Type*} [Fintype I]
    (ε : I → ℝ) (L₀ : ℕ) {P Q : ℝ} (hε : ∀ i, 0 < ε i) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hεQ : ∀ i, (ε i)⁻¹ ≤ Real.exp Q) (hL₀ : (L₀ : ℝ) ≤ Real.exp P) :
    (commonPolynomialInitialScale L₀ ε : ℝ) ≤ Real.exp (P+Q+17) := by
  simp only [commonPolynomialInitialScale, Nat.cast_max, Nat.cast_one]
  refine max_le (hL₀.trans (Real.exp_le_exp.mpr (by linarith)))
    (max_le (Real.one_le_exp (by positivity)) ?_)
  apply natFinsetSup_cast_le _ _ (Real.exp_nonneg _)
  exact fun i _ => integerPolynomialInitialScale_exp_bound (hε i) hP hQ hA (hεQ i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem selectedLayerSamplerScale_bounds (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (hσ : ∀ j, 0 < σ j) (L₀ : ℕ) :
    L₀ ≤ (selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀).value ∧
      (selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀).value ≤
        layerSamplerScaleBound (G := G) B R σ L₀ :=
  (exists_layerSamplerScale (G := G) B U b R σ hR hσ L₀).choose_spec

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem principalSamplingGapRatio_antitone {γ δ : ℝ}
    (hγ : 0 < γ) (hγδ : γ ≤ δ) :
    principalSamplingGapRatio δ ≤ principalSamplingGapRatio γ := by
  apply Nat.ceil_mono
  apply max_le_max le_rfl
  exact div_le_div_of_nonneg_left (by positivity) hγ hγδ

namespace VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_layerSamplerWitnessScale
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      L₀ ≤ S.value ∧ S.value ≤ layerSamplerWitnessScaleBound (G := G) B R σ L₀ W ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j,i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  let γ := layerSamplerGapWidth (G := G) B R
  have hγ (a : Σ j, Fin (n j)) : 0 < γ a := principalProfileSize_pos (hR a.1) _
  obtain ⟨L, hL, hlo, hhi, hw, hg⟩ := exists_common_polynomial_scale
    (fun a : Σ j, Fin (n j) => basisAxisScale (b a.1) a.2) (fun a => a.1.val + 1)
    (fun a => γ a / W) (layerSamplerTailWidth (G := G) B R σ)
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) L₀
  have hgap (j : Fin m) (i : Fin (n j)) (ha : L ^ (j.val + 1) < basisAxisScale (b j) i) :
      (principalSamplingGapRatio (γ ⟨j,i⟩) * L) ^ (j.val + 1) ≤ basisAxisScale (b j) i := by
    have hm := principalSamplingGapRatio_antitone (div_pos (hγ ⟨j,i⟩) hW0)
      (div_le_self (hγ ⟨j,i⟩).le hW)
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hm) _).trans (hg ⟨j,i⟩ ha)
  let S : LayerSamplerScale (G := G) B U b R σ := ⟨L, hL, hw, hgap⟩
  refine ⟨S, hlo, hhi, ?_⟩
  intro j i ha
  have hh := integerAxisPrincipal_width (Nat.zero_lt_succ _) hL
    (div_pos (hγ ⟨j,i⟩) hW0) (hg ⟨j,i⟩ ha)
  have hmul := mul_le_mul_of_nonneg_right hh hW0.le
  have he : ((γ ⟨j,i⟩ / W / 2) *
      ((basisAxisScale (b j) i : ℝ) / (L : ℝ) ^ (j.val + 1))) * W =
      (γ ⟨j,i⟩ / 2) * ((basisAxisScale (b j) i : ℝ) / (L : ℝ) ^ (j.val + 1)) := by
    field_simp
  exact hmul.trans_eq he

theorem layerSamplerWitnessScaleBound_exp_bound
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) {W P Qt Qg Qw : ℝ}
    (hW : 0 < W) (hP : 0 ≤ P) (hQt : 0 ≤ Qt) (hQg : 0 ≤ Qg) (hQw : 0 ≤ Qw)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hL : (L₀ : ℝ) ≤ Real.exp P)
    (ht : ∀ j, (layerSamplerTailWidth (G := G) B R σ j)⁻¹ ≤ Real.exp Qt)
    (hg : ∀ a, (layerSamplerGapWidth (G := G) B R a)⁻¹ ≤ Real.exp Qg)
    (hw : W ≤ Real.exp Qw) :
    (layerSamplerWitnessScaleBound (G := G) B R σ L₀ W : ℝ) ≤
      Real.exp ((P + Qt + 17) + (Fintype.card (Σ j, Fin (n j)) : ℝ) *
        (P + (Qg + Qw) + 17)) := by
  let γ := layerSamplerGapWidth (G := G) B R
  have hγ (a : Σ j, Fin (n j)) : 0 < γ a := principalProfileSize_pos (hR a.1) _
  have hi := commonPolynomialInitialScale_exp_bound
    (layerSamplerTailWidth (G := G) B R σ) L₀
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) hP hQt hA ht hL
  have hginv (a : Σ j, Fin (n j)) : (γ a / W)⁻¹ ≤ Real.exp (Qg + Qw) := by
    rw [inv_div, div_eq_mul_inv, Real.exp_add]
    calc
      _ ≤ Real.exp Qw * Real.exp Qg := mul_le_mul hw (hg a) (inv_nonneg.mpr (hγ a).le)
        (Real.exp_nonneg _)
      _ = _ := mul_comm _ _
  have hgap := commonPolynomialGapRatio_exp_bound (fun a => γ a / W)
    (fun a => div_pos (hγ a) hW) hP (add_nonneg hQg hQw) hA hginv
  unfold layerSamplerWitnessScaleBound
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (P + Qt + 17) *
        (Real.exp (P + (Qg + Qw) + 17)) ^ Fintype.card (Σ j, Fin (n j)) := by
      apply mul_le_mul hi (pow_le_pow_left₀ (Nat.cast_nonneg _) hgap _) (by positivity)
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem allocatedScaleLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ allocatedScaleLog P := by
  unfold allocatedScaleLog
  positivity

theorem le_allocatedScaleLog {P : ℝ} (hP : 0 ≤ P) : P ≤ allocatedScaleLog P := by
  have h : 0 ≤ P^2*(5*P+49) := by positivity
  unfold allocatedScaleLog
  nlinarith

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem layerSamplerWidths_inverse_exp_bounds (R σ : Fin m → ℝ) {P : ℝ}
    (hP : 0 ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P) :
    (∀ j, (layerSamplerTailWidth (G := G) B R σ j)⁻¹ ≤ Real.exp (4*(P+8))) ∧
      (∀ a, (layerSamplerGapWidth (G := G) B R a)⁻¹ ≤ Real.exp (4*(P+8))) := by
  constructor
  · intro j
    exact (allocatedProfile_inverse_exp_bounds _ hP (hR j) (hσ j) (hRP j) (hσP j) (hcount j)).2.2.2
  · intro a
    have hc : ((layerIntegerPrincipalSlots (G := G) B a.1 a.2).card : ℝ) ≤ P :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcount a.1)
    exact (allocatedProfile_inverse_exp_bounds _ hP (hR a.1) (hσ a.1)
      (hRP a.1) (hσP a.1) hc).2.1

theorem layerSamplerScaleBound_exp (R σ : Fin m → ℝ) (L₀ : ℕ) {P : ℝ}
    (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL₀ : (L₀ : ℝ) ≤ Real.exp P) :
    (layerSamplerScaleBound (G := G) B R σ L₀ : ℝ) ≤ Real.exp (allocatedScaleLog P) := by
  obtain ⟨ht, hg⟩ := layerSamplerWidths_inverse_exp_bounds B R σ hP hR hσ hRP hσP hcount
  have hinit := commonPolynomialInitialScale_exp_bound (layerSamplerTailWidth (G := G) B R σ) L₀
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) hP (by positivity) hA ht hL₀
  have hgap := commonPolynomialGapRatio_exp_bound (layerSamplerGapWidth (G := G) B R)
    (fun a => principalProfileSize_pos (hR a.1) _) hP (by positivity) hA hg
  have haxes : (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ P^2 := by
    calc
      _ = ∑ j : Fin m, (n j : ℝ) := by simp [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hn j)
      _ = (m : ℝ)*P := by simp
      _ ≤ P^2 := by nlinarith
  have hp := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg _) hgap (by positivity)
    (Fintype.card (Σ j : Fin m, Fin (n j))) haxes
  simp only [layerSamplerScaleBound, Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (P+4*(P+8)+17) * Real.exp (P^2*(P+4*(P+8)+17)) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedScaleLog; ring

theorem selectedLayerSamplerScale_exp_bound
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL₀ : (L₀ : ℝ) ≤ Real.exp P) :
    ((selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀).value : ℝ) ≤
      Real.exp (allocatedScaleLog P) :=
  (Nat.cast_le.mpr (selectedLayerSamplerScale_bounds B U b R σ hR hσ L₀).2).trans
    (layerSamplerScaleBound_exp B R σ L₀ hP hm hn hR hσ hRP hσP hcount hA hL₀)

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct
namespace OAI

section

namespace Erdos3

theorem quantitativeBadPrimeRadius_error {E : ℝ} (hE : 0 ≤ E) (Q : ℕ) (hQ : 1 ≤ Q) :
    let R := quantitativeBadPrimeRadius E
    0 < Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) ∧
    2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))) ≤ Real.exp (-E) := by
  dsimp only
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : 0 < (Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  have heq : ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2) *
      (Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))) =
      Real.exp (-E) / 2 := by field_simp
  rw [heq]
  linarith [(quantitativeBadPrimeRadius_bounds hE).2.2]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SmoothSpatialCostBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem smoothSpatialDisplacementCost_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) (M : ℕ) :
    0 ≤ smoothSpatialDisplacementCost N s M := by
  unfold smoothSpatialDisplacementCost spatialKernelErrorConstant
    scalarSpatialIndexAllowance scalarSpatialInverseAllowance
  positivity

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem spatialKernelErrorConstant_le_exp (j e : ℕ) {U P : ℝ} (K : ℝ≥0)
    (hU0 : 0 ≤ U) (hU : U ≤ Real.exp P) (hK : (K : ℝ) ≤ Real.exp P) :
    spatialKernelErrorConstant j e U 1 K ≤
      Real.exp ((j : ℝ)^2+(j+2)*P+2*e) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold spatialKernelErrorConstant
  norm_num only [mul_one]
  calc
    _ ≤ (Real.exp ((j : ℝ)^2)*(Real.exp P)^j)*(Real.exp 2)^e*Real.exp P*Real.exp P := by
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      ring

theorem smoothSpatialDisplacementCost_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (N : Type*) [Fintype N] (s : I ↪ J) {M : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ Real.exp p) :
    smoothSpatialDisplacementCost N s M ≤
      Real.exp (spatialDisplacementLog (Fintype.card (Unit ⊕ I))
        (Fintype.card (UnselectedColumn s ⊕ N)) (Fintype.card (UnselectedColumn s))
        (Fintype.card N) p) := by
  let j := Fintype.card (Unit ⊕ I)
  let d := Fintype.card (UnselectedColumn s ⊕ N)
  let e := Fintype.card (UnselectedColumn s)
  let P := spatialProfileLog j d p
  obtain ⟨hG, hU, _, hK⟩ := spatialProfileLog_bounds N s hp hM
  have he : (e : ℝ) ≤ d := by
    simp only [d, e, Fintype.card_sum, Nat.cast_add]
    exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hsmall : ((e+j : ℝ)*probabilityProfileLipschitz) ≤ Real.exp P := by
    apply le_trans _ hK
    gcongr
  have hc := spatialKernelErrorConstant_le_exp j e ((e+j)*probabilityProfileLipschitz)
    (by unfold scalarSpatialInverseAllowance; positivity) hU
    (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast] using hsmall)
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  unfold smoothSpatialDisplacementCost
  calc
    _ ≤ Real.exp P * Real.exp ((j : ℝ)^2+(j+2)*P+2*e) * Real.exp (Fintype.card N : ℝ) := by
      apply mul_le_mul _ hn (Nat.cast_nonneg _) (by positivity)
      exact mul_le_mul hG hc (by unfold spatialKernelErrorConstant scalarSpatialInverseAllowance; positivity)
        (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [spatialDisplacementLog, P]
      ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CanonicalDetectedScaleInputBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem natCeil_le_exp_succ_of_le {x p : ℝ} (hp : 0 ≤ p) (hx : x ≤ Real.exp p) :
    (⌈x⌉₊ : ℝ) ≤ Real.exp (p+1) := by
  calc
    _ ≤ (⌈Real.exp p⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_mono hx
    _ ≤ Real.exp p+1 := (Nat.ceil_lt_add_one (Real.exp_pos p).le).le
    _ = 1+Real.exp p := add_comm _ _
    _ ≤ _ := one_add_le_exp_succ hp le_rfl

end Erdos3

end

section

namespace Erdos3

theorem slicedDetectionGain_lower (s C count : ℕ) {p q a α : ℝ}
    (hα : Real.exp (-a) ≤ α) :
    Real.exp (-slicedDetectionGainLog s C count p q a) ≤
      (Real.exp (-((5 * p + 20) * count + p + 2)) * (α / 2)) *
        Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
  have hhalf : Real.exp (-(a + 1)) ≤ α / 2 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh : 2 * Real.exp (-(a + 1)) ≤ Real.exp (-a) := by
      calc
        _ ≤ Real.exp 1 * Real.exp (-(a + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    linarith
  calc
    _ = (Real.exp (-((5 * p + 20) * count + p + 2)) * Real.exp (-(a + 1))) *
          Real.exp (-((q + C) ^ C)) ^ (2 ^ (s + 1)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold slicedDetectionGainLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg _)) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalBadProductErrorBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem physicalBadProductAccuracy_pos (E Vlog : ℝ) :
    0 < physicalBadProductAccuracy E Vlog := Real.exp_pos _

theorem physicalBadProductAccuracy_inv (E Vlog : ℝ) :
    (physicalBadProductAccuracy E Vlog)⁻¹ = Real.exp (Vlog + 3 * E + 16) := by
  unfold physicalBadProductAccuracy
  rw [Real.exp_neg, inv_inv]

private theorem exp_eight_ge : (128 : ℝ) ≤ Real.exp 8 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 8
  have he : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
    simp
  rw [he]
  norm_num at hpow ⊢
  linarith

theorem physicalBadProductAccuracy_budget {E Vlog : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    let κ := physicalBadProductAccuracy E Vlog
    let R := quantitativeBadPrimeRadius E
    let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
    0 < κ ∧ κ⁻¹ = Real.exp (Vlog + 3 * E + 16) ∧
      2 * κ + κ ≤ 1 / 2 ∧ 128 * κ ≤ η ∧
      12 * (2 * κ + κ) + κ ≤ η := by
  dsimp only
  let T := Vlog + 3 * E + 8
  let η := Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))
  have hη : 0 < η := (quantitativeBadPrimeRadius_error hE Q hQ).1
  have hi : 1 / η ≤ Real.exp T :=
    (quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp).2
  have hlo : Real.exp (-T) ≤ η := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos T)).mpr
    have hh := (div_le_iff₀ hη).mp hi
    simpa only [mul_comm] using hh
  have heq : physicalBadProductAccuracy E Vlog = Real.exp (-T) / Real.exp 8 := by
    rw [physicalBadProductAccuracy, ← Real.exp_sub]
    congr 1
    dsimp [T]
    ring
  have h128 : 128 * physicalBadProductAccuracy E Vlog ≤ η := by
    rw [heq]
    apply le_trans _ hlo
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.exp_pos 8)).mpr
    have h := mul_le_mul_of_nonneg_left exp_eight_ge (Real.exp_pos (-T)).le
    nlinarith
  have hκ := physicalBadProductAccuracy_pos E Vlog
  have hκsmall : physicalBadProductAccuracy E Vlog ≤ 1 / 128 := by
    have hT : 0 ≤ T := by dsimp [T]; linarith
    have hl : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
    have hh : physicalBadProductAccuracy E Vlog * Real.exp 8 = Real.exp (-T) := by
      rw [heq, div_mul_cancel₀ _ (Real.exp_pos 8).ne']
    have h := mul_le_mul_of_nonneg_left exp_eight_ge hκ.le
    nlinarith
  refine ⟨hκ, physicalBadProductAccuracy_inv E Vlog, ?_, h128, ?_⟩
  · linarith
  · linarith

theorem physicalBadProductGap_budget (N : ℕ) {E Vlog : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    1 ≤ physicalBadProductGap N E Vlog Q ∧
    (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) ≤ physicalBadProductGap N E Vlog Q ∧
    2 * (N : ℝ) * (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) /
      physicalBadProductAccuracy E Vlog ≤ physicalBadProductGap N E Vlog Q := by
  have hb := physicalBadProductAccuracy_budget hE hVlog Q hQ hQexp
  have hκ := hb.1
  have hκ1 : physicalBadProductAccuracy E Vlog ≤ 1 := by linarith [hb.2.2.1]
  have hc : (1 : ℝ) ≤ (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) := by
    exact_mod_cast hQ.trans (le_max_left _ _)
  have hW : (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) ≤ physicalBadProductGap N E Vlog Q := by
    unfold physicalBadProductGap
    apply (le_div_iff₀ hκ).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  refine ⟨hc.trans hW, hW, ?_⟩
  unfold physicalBadProductGap
  exact div_le_div_of_nonneg_right (by nlinarith) hκ.le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_allocatedWitnessScale_of_bounded_source
    (R σ : Fin m → ℝ) (S0 : LayerSamplerScale (G := G) B U b R σ)
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D P W Qw : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hDQ : D ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hS0 : (S0.value : ℝ) ≤ Real.exp P)
    (hW : 1 ≤ W) (hQw : 0 ≤ Qw) (hWexp : W ≤ Real.exp Qw) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S0.value ≤ S.value ∧
      (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog P Qw) ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDQ
  have hm : (m : ℝ) ≤ P := hdim.degree.trans hDQ
  have hn (j : Fin m) : (n j : ℝ) ≤ P := by
    have hi : Function.Injective (fun i : Fin (n j) =>
        (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) := by
      intro a b hab
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Sum.inr.injEq] using hab
    have hc := Fintype.card_le_of_injective _ hi
    exact (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hc)).trans
      (hdim.axes.trans hDQ)
  have haxes : (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ P ^ 2 := by
    calc
      _ = ∑ j : Fin m, (n j : ℝ) := by simp [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hn j)
      _ = (m : ℝ) * P := by simp
      _ ≤ P ^ 2 := by nlinarith
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P :=
    (hdim.profile.trans hDQ).trans (by linarith [Real.add_one_le_exp P])
  obtain ⟨ht, hg⟩ := layerSamplerWidths_inverse_exp_bounds B R σ hP hR hσ hRi hσi
    (fun j => (hdim.coefficients j).trans hDQ)
  have hbound := layerSamplerWitnessScaleBound_exp_bound B R σ hR hσ S0.value
    (lt_of_lt_of_le zero_lt_one hW) hP (show 0 ≤ 4 * (P + 8) by positivity)
    (show 0 ≤ 4 * (P + 8) by positivity) hQw hA hS0 ht hg hWexp
  obtain ⟨S, hle, hS, hwidth⟩ :=
    exists_layerSamplerWitnessScale (G := G) B U b R σ hR hσ S0.value hW
  refine ⟨S, hle, (Nat.cast_le.mpr hS).trans (hbound.trans ?_), hwidth⟩
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (P + 4 * (P + 8) + 17) + P ^ 2 * (P + (4 * (P + 8) + Qw) + 17) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right haxes
        (show 0 ≤ P + (4 * (P + 8) + Qw) + 17 by positivity))
    _ = allocatedWitnessScaleLog P Qw := by
      unfold allocatedWitnessScaleLog allocatedScaleLog
      ring

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealRefinedPointwise
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem AllocatedComparisonDimensions.integer_axes {D : ℝ}
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (n j : ℝ) ≤ D := by
  have hi : Function.Injective (fun i : Fin (n j) =>
      (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) := by
    intro a b hab
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Sum.inr.injEq] using hab
  have hc := Fintype.card_le_of_injective _ hi
  exact (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hc)).trans h.axes

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SpatialNumericEnvelopeFunctoriality
namespace OAI

section

namespace Erdos3

theorem spatialPrimitiveEnvelope_bounds {p E l : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) :
    let R := spatialPrimitiveEnvelope p E l
    0 ≤ R ∧ p ≤ R ∧ E + 3 ≤ R ∧ p ^ 3 + anisotropicSpatialCapLog p ≤ R ∧
      coefficientErrorVolumeLog p + 4 ≤ R ∧ spatialDisplacementEnvelope p ≤ R ∧
      spatialDiscretizationEnvelope p l ≤ R ∧ spatialLipschitzCostEnvelope p l ≤ R ∧
      spatialThresholdEnvelope p l ≤ R ∧ spatialBoundaryEnvelope p l ≤ R ∧
      spatialMovementEnvelope p l ≤ R := by
  obtain ⟨_, hd, ha, hm, hk⟩ := spatialCostEnvelopes_nonneg hp hl
  have hcap : 0 ≤ p ^ 3 + anisotropicSpatialCapLog p := by
    have := anisotropicSpatialCapLog_nonneg hp
    positivity
  have hvol : 0 ≤ coefficientErrorVolumeLog p + 4 := by
    unfold coefficientErrorVolumeLog
    positivity
  have hK : 0 ≤ spatialLipschitzCostEnvelope p l := by
    unfold spatialLipschitzCostEnvelope
    positivity
  have hT : 0 ≤ spatialThresholdEnvelope p l := by
    unfold spatialThresholdEnvelope
    positivity
  have hQ : 0 ≤ spatialBoundaryEnvelope p l := by
    unfold spatialBoundaryEnvelope
    positivity
  have hD : 0 ≤ spatialMovementEnvelope p l := by
    unfold spatialMovementEnvelope
    positivity
  dsimp only [spatialPrimitiveEnvelope]
  repeat' constructor
  all_goals linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedTupleParameterBounds
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem normalizedSpatialShare_half_inv_le (E : ℝ) :
    (normalizedSpatialShare E / 2)⁻¹ ≤ Real.exp (E + 3) := by
  unfold normalizedSpatialShare
  rw [inv_div, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  calc
    _ ≤ Real.exp 1 * Real.exp (E + 2) := mul_le_mul_of_nonneg_right
      (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem normalizedTupleEarlyParameters_bound {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q M : ℕ} (s : Fin q ↪ G)
    {p E l : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l)
    (hMp : (M : ℝ) ≤ Real.exp p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hN : (Fintype.card N : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    let R := spatialPrimitiveEnvelope p E l
    (normalizedTupleTolerance X p E)⁻¹ ≤ Real.exp (spatialTupleToleranceLog R) ∧
      (normalizedTupleNarrowWidth X N s M p E)⁻¹ ≤
        Real.exp (2 * (R + spatialTupleToleranceLog R) + 4) := by
  obtain ⟨hR, hpR, hER, hcapR, hvolR, hdispR, _⟩ :=
    spatialPrimitiveEnvelope_bounds hp hE hl
  obtain ⟨he, hd, _⟩ := spatialAuxiliaryDimensions (N := N) s hG hN
  have hI : (Fintype.card (Unit ⊕ Fin q) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hq
  have hB := (smoothSpatialDisplacementCost_le_exp N s hp hMp).trans
    (Real.exp_le_exp.mpr ((spatialDisplacementLog_le_envelope _ _ _ _ hp hI hd he hN).trans hdispR))
  have hε : 0 < normalizedSpatialShare E / 2 := half_pos (Real.exp_pos _)
  have hεR := (normalizedSpatialShare_half_inv_le E).trans (Real.exp_le_exp.mpr hER)
  exact ⟨spatialTupleTolerance_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
    hε hR (hX.trans hpR) (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hεR,
    spatialTupleEarlyWidth_inv_bound (Fintype.card X) (Real.exp_nonneg _) (Real.exp_nonneg _)
      (smoothSpatialDisplacementCost_nonneg N s M) hε hR (hX.trans hpR)
      (Real.exp_le_exp.mpr hcapR) (Real.exp_le_exp.mpr hvolR) hB hεR⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedAffineLengthLog_kernel_bound {m : ℕ} (hm : 0 < m)
    {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T) :
    Pk ≤ allocatedAffineLengthLog m D P Prho Pk target F T := by
  let L := allocatedAffineL1Log m D P Prho Pk
  have hL : 0 ≤ L := allocatedAffineL1Log_nonneg m hD hP hr hk
  have hd := allocatedDensityEnvelope_nonneg m hD hP
  have hs := allocatedSupportEnvelope_nonneg m hD hP
  have hi : 0 ≤ allocatedIdealLipEnvelope D P Prho := by
    unfold allocatedIdealLipEnvelope
    positivity
  have hb : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
  have hc : (1 : ℝ) ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hm (pow_pos (by decide : 0 < (2 : ℕ)) _))
  have hkL : Pk ≤ L := by
    have hprod := mul_le_mul_of_nonneg_right hc hk
    dsimp only [L, allocatedAffineL1Log]
    have hrad : 0 ≤ ((m + 1 : ℕ) : ℝ) * D := mul_nonneg (Nat.cast_nonneg _) hD
    nlinarith
  have hLE : L ≤ allocatedAffineReferenceAccuracyLog m D P Prho Pk target := by
    have hp := mul_nonneg hD (add_nonneg hL zero_le_one)
    dsimp only [allocatedAffineReferenceAccuracyLog, affineReferenceCoefficientLog]
    change L ≤ target + 1 + 8 * (D + 1) * (L + 1) + 4
    nlinarith
  exact hkL.trans (hLE.trans (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.2.1)

theorem allocatedAffineLength_kernel_ready {m : ℕ} (hm : 0 < m)
    {D P Prho Pk target F T : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk)
    (ht : 0 ≤ target) (hF : 0 ≤ F) (hT : 0 ≤ T)
    {Mk S : ℕ} (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (hS : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤ (S : ℝ)) : Mk ≤ S := by
  exact_mod_cast hMk.trans ((Real.exp_le_exp.mpr
    (allocatedAffineLengthLog_kernel_bound hm hD hP hr hk ht hF hT)).trans hS)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AveragedNormalizedTwistForecastJointModel
namespace OAI

section

namespace Erdos3

theorem forecastAugmentedUnitThreshold_half_source_precision {u p K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p) (hFp : Fcap ≤ Real.exp p) :
    Real.exp (-(2 * (u + 1) + 4 * p + 7)) ≤
      forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  calc
    _ = Real.exp (-(2 * u + 4 * p + 8)) / Real.exp 1 := by
      rw [← Real.exp_sub]; congr 1; ring
    _ ≤ Real.exp (-(2 * u + 4 * p + 8)) / 2 :=
      div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)])
    _ ≤ _ := div_le_div_of_nonneg_right
      (forecastAugmentedUnitThreshold_bounds hu hp hK hC hKp hCp hFp).2.2 (by norm_num)

end Erdos3

end

section

namespace Erdos3

theorem forecastAugmented_separate_source_precision {u p pSource K C Fcap : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hSource : 0 ≤ pSource)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hKp : K ≤ Real.exp p) (hCp : C ≤ Real.exp p)
    (hFp : Fcap ≤ Real.exp p) :
    0 ≤ u + 2 * p + 1 ∧
      Real.exp (-(2 * (u + 2 * p + 1) + 4 * pSource + 7)) ≤
        forecastAugmentedUnitThreshold u p K C Fcap / 2 := by
  refine ⟨by positivity, ?_⟩
  apply (Real.exp_le_exp.mpr
    (show -(2 * (u + 2 * p + 1) + 4 * pSource + 7) ≤
      -(2 * (u + 1) + 4 * p + 7) by linarith)).trans
  exact forecastAugmentedUnitThreshold_half_source_precision hu hp hK hC hKp hCp hFp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastPreparedScaleBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedSamplerBlockCount_jets (m dim : ℕ) (j : Fin m) :
    Fintype.card (BoundedBooleanJet (Fin dim) (j.val + 1)) ≤ preparedSamplerBlockCount m dim j := by
  dsimp only [preparedSamplerBlockCount]
  omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem preparedCommonBlockCount_jets (m : ℕ) (j : Fin m) (s : Fin (m + 1)) :
    Fintype.card (BoundedBooleanJet (Fin (s.val + 1)) (j.val + 1)) ≤ preparedCommonBlockCount m j :=
  (preparedSamplerBlockCount_jets m (s.val + 1) j).trans (preparedCommonBlockCount_ge m j s)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem enlargedPreparedCommonSamplerBlock_jets (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    Fintype.card (BoundedBooleanJet (Fin (s + 1)) (a.1.val + 1)) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  simpa only [EnlargedPreparedCommonSamplerBlock, Fintype.card_fin] using
    (preparedCommonBlockCount_jets m a.1 ⟨s, Nat.lt_succ_of_le hs⟩).trans
      (Nat.le_add_right _ Jalloc)

theorem enlargedPreparedCommonSamplerBlock_positiveModerate (Jalloc s : ℕ) (hs : s ≤ m)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    let rows := boundedBooleanJetRows (Fin (s + 1)) (a.1.val + 1)
    positiveModerateSpectrumBlockCount a.1.val rows.card ((layerTailDegree m + 1) * rows.card) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  dsimp only
  apply le_trans _ ((le_max_left _ _).trans
    (enlargedPreparedCommonSamplerBlock_spectrum L Jalloc s hs a))
  unfold positiveModerateSpectrumBlockCount
  apply Nat.succ_le_succ
  apply max_le_max (le_refl _)
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeTolerance
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem preparedUniformDegreeTolerance_bounds (t Ptail : ι → ℝ)
    {pRadius Qσ : ℝ} (ht : ∀ i, 0 < t i) (ht1 : ∀ i, t i ≤ 1)
    (hPtail : ∀ i, 0 ≤ Ptail i) (hinv : ∀ i, (t i)⁻¹ ≤ Real.exp (Ptail i))
    (hQσ : 0 ≤ Qσ) (hpRadius : 0 ≤ pRadius) :
    let σ := preparedUniformDegreeTolerance t Qσ
    let Pscale := preparedUniformDegreeScaleLog pRadius Ptail Qσ
    0 < σ ∧ σ ≤ 1 ∧ (∀ i, σ ≤ t i) ∧ σ ≤ Real.exp (-Qσ) ∧
      σ⁻¹ ≤ Real.exp Pscale ∧ 0 ≤ Pscale ∧ (∀ i, Ptail i ≤ Pscale) := by
  classical
  dsimp only
  have hprod : 0 < ∏ i, t i := Finset.prod_pos (fun i _ => ht i)
  have hprod1 : ∏ i, t i ≤ 1 :=
    Finset.prod_le_one (fun i _ => (ht i).le) (fun i _ => ht1 i)
  have hprodi (i : ι) : ∏ j, t j ≤ t i := by
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ {i})
        (fun j _ => (ht j).le) (fun j _ _ => ht1 j))
  have hsum : 0 ≤ ∑ i, Ptail i := Finset.sum_nonneg (fun i _ => hPtail i)
  have hsumScale : (∑ i, Ptail i) ≤ preparedUniformDegreeScaleLog pRadius Ptail Qσ := by
    unfold preparedUniformDegreeScaleLog
    linarith only [hpRadius, hQσ]
  have hQScale : Qσ ≤ preparedUniformDegreeScaleLog pRadius Ptail Qσ := by
    unfold preparedUniformDegreeScaleLog
    linarith only [hpRadius, hsum]
  have hprodInv : (∏ i, t i)⁻¹ ≤ Real.exp (∑ i, Ptail i) := by
    rw [← Finset.prod_inv_distrib, Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (ht i).le) (fun i _ => hinv i)
  refine ⟨lt_min hprod (Real.exp_pos _), (min_le_left _ _).trans hprod1,
    fun i => (min_le_left _ _).trans (hprodi i), min_le_right _ _, ?_,
    hsum.trans hsumScale, ?_⟩
  · unfold preparedUniformDegreeTolerance
    rcases le_total (∏ i, t i) (Real.exp (-Qσ)) with h | h
    · rw [min_eq_left h]
      exact hprodInv.trans (Real.exp_le_exp.mpr hsumScale)
    · rw [min_eq_right h, ← Real.exp_neg, neg_neg]
      exact Real.exp_le_exp.mpr hQScale
  · intro i
    exact (Finset.single_le_sum (fun j _ => hPtail j) (Finset.mem_univ i)).trans hsumScale

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedDetectedCanonicalNativeSource
namespace OAI

section

namespace Erdos3
open scoped NNReal

private theorem prepared_jointAffineSourceEnvelope_ge_accuracy {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    E ≤ jointAffineSourceEnvelope D P E F := by
  have hInv : 0 ≤ jointAffineInverseEnvelope D P E F := by
    have := affineInverseAxisEnvelope_nonneg hD hP hE hF
    unfold jointAffineInverseEnvelope
    positivity
  have hDer : 0 ≤ jointAffineDerivativeEnvelope D P := by
    have := affineDerivativeAxisEnvelope_nonneg hD hP
    unfold jointAffineDerivativeEnvelope
    positivity
  have hWeight : 0 ≤ jointAffineWeightEnvelope D P E F := by
    have := affineWeightAxisEnvelope_nonneg hD hP hE hF
    unfold jointAffineWeightEnvelope
    positivity
  have hOut := mul_nonneg hD hD
  have hParam := mul_nonneg hD (affineMinorVariableEnvelope_nonneg hD)
  dsimp only [jointAffineSourceEnvelope]
  linarith

theorem prepared_affineProfileToleranceEnvelope_ge_accuracy (degree : ℕ)
    {D N E F : ℝ} (A T : ℝ≥0)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    E ≤ affineProfileToleranceEnvelope degree D N (A : ℝ) (T : ℝ) E F := by
  have hC : 0 ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold affineProfileCoefficientEnvelope
    positivity
  have hInput : E ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F := by
    exact (by linarith : E ≤ E + D + 4).trans
      (prepared_jointAffineSourceEnvelope_ge_accuracy hD hC (by positivity) hF)
  have hRest : 0 ≤ 3 * N * (degree + 2 : ℕ) +
      (2 * (D + affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) + degree * D) + 1) := by
    positivity
  unfold affineProfileToleranceEnvelope
  linarith

namespace VectorPolynomial

theorem allocatedAffineLengthLog_mono_density (m : ℕ)
    {D P Prho Pk target F F' Tmod : ℝ} (hF : F ≤ F') :
    allocatedAffineLengthLog m D P Prho Pk target F Tmod ≤
      allocatedAffineLengthLog m D P Prho Pk target F' Tmod := by
  dsimp only [allocatedAffineLengthLog, progressionSliceLengthLog]
  linarith

theorem allocatedAffineLengthLog_prepared_density (m : ℕ)
    (D P Prho Pk target p Tmod : ℝ) :
    allocatedAffineLengthLog m D P Prho Pk target (p + 1) Tmod ≤
      allocatedAffineLengthLog m D P Prho Pk target (p + 2) Tmod :=
  allocatedAffineLengthLog_mono_density m (by linarith)

theorem prepared_affineProfileToleranceEnvelope_kernel_bound {m : ℕ} (hm : 0 < m)
    {D Pk target p : ℝ} (A T : ℝ≥0)
    (hD : 1 ≤ D) (hk : 0 ≤ Pk) (ht : 0 ≤ target) (hp : 0 ≤ p) :
    Pk ≤ affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (A : ℝ) (T : ℝ) (target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5) (p + 2) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hc : (1 : ℝ) ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_pos hm (pow_pos (by decide : 0 < (2 : ℕ)) _))
  have hkC : Pk ≤ (m * 2 ^ (m + 1) : ℕ) * Pk := by
    simpa using mul_le_mul_of_nonneg_right hc hk
  have hCD : (m * 2 ^ (m + 1) : ℕ) * Pk ≤
      D * ((m * 2 ^ (m + 1) : ℕ) * Pk) := by
    simpa using mul_le_mul_of_nonneg_right hD (by positivity :
      0 ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk)
  have hE : Pk ≤ target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5 := by
    linarith
  exact hE.trans (prepared_affineProfileToleranceEnvelope_ge_accuracy m A T hD0
    (by positivity) (hk.trans hE) (by positivity))

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralProductivityEarlyGain
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

private theorem allocatedAffineCoveredComparison_instances
    {m : ℕ} {G : Type} [fG : Fintype G] [dG : DecidableEq G]
    {I : Fin m → Type} [fI : ∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [fB : ∀ a, Fintype (B a)]
    {α : Type} [fα : Fintype α] [dα : DecidableEq α] {O : Fin m → Type}
    {dB₁ dB₂ : ∀ a, DecidableEq (B a)}
    {fO₁ fO₂ : ∀ j, Fintype (O j)} {dO₁ dO₂ : ∀ j, DecidableEq (O j)}
    {rows : ∀ j, O j → Finset α} {δ η : ℝ}
    {ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0} {t : ℝ} {htone : t ≤ 1}
    (h : @AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} m G fG dG I fI n B fB dB₁
      α fα dα O fO₁ dO₁ rows δ η ρ t htone) :
    @AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} m G fG dG I fI n B fB dB₂
      α fα dα O fO₂ dO₂ rows δ η ρ t htone := by
  have hB : dB₁ = dB₂ := Subsingleton.elim _ _
  have hF : fO₁ = fO₂ := Subsingleton.elim _ _
  have hO : dO₁ = dO₂ := Subsingleton.elim _ _
  cases hB
  cases hF
  cases hO
  exact @h

theorem allocatedEarlyNativeSourceGeometryGeneral_of_fields
    {m s nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (Pchart P D target Pk Prho Qstride pDetect : ℝ) (K : ℝ≥0)
    (hP : 0 ≤ P)
    (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hPk : 0 ≤ Pk) (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target (pDetect + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    (η : ℝ) (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{0,0,0,0,0,0,0} (G := G) B
      (fun j : Fin m => (Subtype.val : boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) → Finset (Fin (s + 1))))
      (Real.exp (-(pDetect + 1))) η ρ t htone)
    (hρ : ∀ partition, 0 < ρ partition)
    (hρ1 : ∀ partition, ρ partition ≤ 1)
    (hρlog : ∀ partition, (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho)
    (hσsmall : ∀ j, σ j ≤ t)
    (T : Fin m → ℝ)
    (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) *
          ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (siteRadius : ℝ≥0) (hrone : 1 ≤ siteRadius)
    (hradius : ∀ j, (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card * T j ≤ (siteRadius : ℝ))
    (hbudgets : ∀ C : Fin m → ℝ, (∀ j, 0 ≤ C j) → (∀ j, C j ≤ Real.exp Pchart) →
      (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) ∧
      (∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4) ∧
      (∀ j, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin (s + 1))) *
          (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4))
    (hK : ∀ j, (R j)⁻¹ ≤ K) :
    Nonempty (AllocatedEarlyNativeSourceGeometryGeneral (s := s) (B := B)
      (U := U) (basis := basis) (S := S) (nX := nX)
      Pchart P D target Pk Prho Qstride pDetect K) := by
  refine ⟨{
    hP := hP
    hRP := hRP
    hRi := hRi
    hσi := hσi
    hcount := hcount
    hdimensions := hdimensions
    hPk := hPk
    hPrho := hPrho
    htarget := htarget
    hlength := hlength
    η := η
    hη0 := hη0
    hηsmall := hηsmall
    ρ := ρ
    t := t
    htone := htone
    hs := ?_
    hρ := hρ
    hρ1 := hρ1
    hρlog := hρlog
    hσsmall := hσsmall
    T := T
    hT := hT
    hsource := hsource
    siteRadius := siteRadius
    hrone := hrone
    hradius := hradius
    hbudgets := hbudgets
    hK := hK }⟩
  exact @allocatedAffineCoveredComparison_instances m G _ _ I _ n B _
    (Fin (s + 1)) _ _ (fun j => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type))
    _ _ _ _ _ _ _ (Real.exp (-(pDetect + 1))) η ρ t htone (@hs)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedModularCanonicalDetectorSpatialBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ b, Fintype (B b)]

theorem preparedModularDetector_narrow_width {q Mk nX : ℕ} (selection : Fin q ↪ G)
    {Pphysical coarseTarget : ℝ} (hp : 0 ≤ Pphysical) (htarget : 0 ≤ coarseTarget)
    (hMk : (Mk : ℝ) ≤ Real.exp Pphysical) (hq : ((q + 1 : ℕ) : ℝ) ≤ Pphysical)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pphysical)
    (hnX : (nX : ℝ) ≤ Pphysical) :
    let R := spatialPrimitiveEnvelope Pphysical coarseTarget 0
    let ξLog := 2 * (R + spatialTupleToleranceLog R) + 4
    0 ≤ ξLog ∧
      (normalizedTupleNarrowWidth (Fin nX) (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection Mk Pphysical coarseTarget)⁻¹ ≤ Real.exp ξLog := by
  intro R ξLog
  have hG := (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvars
  have hN := (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvars
  have hX : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical := by simpa only [Fintype.card_fin] using hnX
  have hR : 0 ≤ R := (spatialPrimitiveEnvelope_bounds hp htarget (le_refl 0)).1
  have ht := spatialTupleToleranceLog_nonneg hR
  refine ⟨by dsimp only [ξLog]; positivity, ?_⟩
  exact (normalizedTupleEarlyParameters_bound
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := Fin nX)
    selection hp htarget (le_refl 0) hMk hq hG hN hX).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_preparedUniformDegreeSampler
    {ι : Type*} [Fintype ι] (R σ : Fin m → ℝ) (lengthLogs : ι → ℝ)
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D P Pmin W Qw : ℝ} {Lmin : ℕ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hDP : D ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hLogs : ∀ i, 0 ≤ lengthLogs i)
    (hPmin : 0 ≤ Pmin) (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hW : 1 ≤ W) (hQw : 0 ≤ Qw) (hWexp : W ≤ Real.exp Qw) :
    let Lsum := ∑ i, lengthLogs i
    let Pseed := allocatedScaleLog (P + Lsum + Pmin + 1)
    ∃ S : LayerSamplerScale (G := G) B U basis R σ,
      (∀ i, Real.exp (lengthLogs i) ≤ S.value) ∧
      Lmin ≤ S.value ∧
      (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (basis j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
            ((basisAxisScale (basis j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  intro Lsum Pseed
  let Q := P + Lsum + Pmin + 1
  let L0 := ⌈Real.exp (Lsum + Pmin)⌉₊
  let S0 := selectedLayerSamplerScale (G := G) B U basis R σ hR hσ L0
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hsum : 0 ≤ Lsum := Finset.sum_nonneg (fun i _ => hLogs i)
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith only [hP, hsum, hPmin]
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith only [hsum, hPmin]
  have hLQ : Lsum + Pmin + 1 ≤ Q := by dsimp only [Q]; linarith only [hP]
  have hL0 : (L0 : ℝ) ≤ Real.exp Q :=
    (natCeil_le_exp_succ_of_le (add_nonneg hsum hPmin) le_rfl).trans
      (Real.exp_le_exp.mpr hLQ)
  have hS0 : (S0.value : ℝ) ≤ Real.exp Pseed := by
    apply selectedLayerSamplerScale_exp_bound B U basis R σ hR hσ L0 hQ
      (hdim.degree.trans (hDP.trans hPQ))
      (fun j => (hdim.integer_axes B j).trans (hDP.trans hPQ))
      (fun j => (hRi j).trans (Real.exp_le_exp.mpr hPQ))
      (fun j => (hσi j).trans (Real.exp_le_exp.mpr hPQ))
      (fun j => (hdim.coefficients j).trans (hDP.trans hPQ))
    · exact (hdim.profile.trans (hDP.trans hPQ)).trans
        (by linarith only [Real.add_one_le_exp Q])
    · exact hL0
  have hPSeed : P ≤ Pseed := hPQ.trans (le_allocatedScaleLog hQ)
  obtain ⟨S, hS0S, hS, hgap⟩ := exists_allocatedWitnessScale_of_bounded_source
    B U basis R σ S0 hdim (hDP.trans hPSeed) hR hσ
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hPSeed))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hPSeed))
    hS0 hW hQw hWexp
  have hL0S : L0 ≤ S.value :=
    (selectedLayerSamplerScale_bounds B U basis R σ hR hσ L0).1.trans hS0S
  have hExpS : Real.exp (Lsum + Pmin) ≤ (S.value : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hL0S)
  refine ⟨S, ?_, ?_, hS, hgap⟩
  · intro i
    have hi : lengthLogs i ≤ Lsum :=
      Finset.single_le_sum (fun j _ => hLogs j) (Finset.mem_univ i)
    exact (Real.exp_le_exp.mpr (hi.trans (le_add_of_nonneg_right hPmin))).trans hExpS
  · exact Nat.cast_le.mp (hLmin.trans
      ((Real.exp_le_exp.mpr (le_add_of_nonneg_left hsum)).trans hExpS))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedUniformDegreeDirectLate_extra
    (Pmaster Pscale Pphysical coarseTarget extraLate : ℝ) :
    extraLate ≤ preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate :=
  (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalScalarConstruction
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem preparedFiniteScheduleDirectScalarBounds_explicit
    (m : ℕ) {K : Type*} [Fintype K] (degree Cdetect : K → ℕ)
    (hdegree : ∀ k, degree k ≤ m) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale requestedCoarse extraLate : ℝ)
    (u pModel pSlice Prho : K → ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : ∀ k, 0 ≤ u k) (hmodel : ∀ k, 0 ≤ pModel k) (hstride : 0 ≤ Qstride)
    (hrho : ∀ k, 0 ≤ Prho k) (hslice : ∀ k, pSlice k ≤ pModel k)
    (hcount : ∀ k, (count : ℝ) ≤ Real.exp (pModel k)) :
    let pDetect := fun k => allocatedModelTestLog (u k) (pModel k)
    let gainLog := fun k => slicedDetectionGainLog (degree k) (Cdetect k) count
      (pDetect k) (pDetect k) (2 * u k + 4 * pModel k + 7)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1)) G
      (gainLog k + pDetect k + 4)
    let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ k, Pk k
    let target := fun k => gainLog k + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleDirectMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let coarseTarget := preparedFiniteScheduleDirectCoarse gainLog requestedCoarse
    let Plate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical coarseTarget extraLate
    (∀ k, Pk k ≤ Pscale) → ∀ k,
      PreparedUniformDegreeDirectScalarBounds m (degree k) nX count (Cdetect k)
        Pchart Pscale D (target k) (Pk k) (Prho k) Qstride Pmaster Plate
        (gainLog k) Pphysical coarseTarget pRadius (u k) (pModel k) (pSlice k) := by
  intro pDetect gainLog Pk Pphysical target Pmaster coarseTarget Plate hkernelScale
  have hp (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    have := hu k
    have := hmodel k
    positivity
  have ha (k) : 0 ≤ 2 * u k + 4 * pModel k + 7 := by
    have := hu k
    have := hmodel k
    positivity
  have hg (k) : 0 ≤ gainLog k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) count (hp k) (hp k) (ha k)
  have hk (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hg k
    have := hp k
    positivity
  have hkSum0 : 0 ≤ ∑ k, Pk k := Finset.sum_nonneg (fun k _ => hk k)
  have hkSum (k) : Pk k ≤ ∑ t, Pk t :=
    Finset.single_le_sum (fun t _ => hk t) (Finset.mem_univ k)
  have hphysEq : Pphysical = (m : ℝ) + 2 + nX + count + Qstride + ∑ k, Pk k := by
    simp only [Pphysical, Nat.cast_add, Nat.cast_ofNat]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnX0 : (0 : ℝ) ≤ nX := Nat.cast_nonneg nX
  have hcount0 : (0 : ℝ) ≤ count := Nat.cast_nonneg count
  have hphysical0 : 0 ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum0]
  have hkernelPhysical (k) : Pk k ≤ Pphysical := by
    linarith only [hphysEq, hm0, hnX0, hcount0, hstride, hkSum k]
  have herror0 := coefficientErrorSpatialLog_nonneg hphysical0
  have ht (k) : 0 ≤ target k := by
    dsimp only [target]
    have := hg k
    positivity
  let total := ∑ k, (u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32)
  have hentry (k) : 0 ≤ u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 := by
    have := hu k
    have := hmodel k
    have := hp k
    have := hrho k
    have := ht k
    have := hg k
    positivity
  have htotal0 : 0 ≤ total := Finset.sum_nonneg (fun k _ => hentry k)
  have htotal (k) : u k + pModel k + pDetect k + Prho k + target k + gainLog k + 32 ≤ total :=
    Finset.single_le_sum (fun k _ => hentry k) (Finset.mem_univ k)
  have hmasterEq : Pmaster = Pchart + D + pRadius + Qstride + Pphysical + total := rfl
  have hmaster0 : 0 ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0, htotal0]
  have hphysicalMaster : Pphysical ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, htotal0]
  have htotalMaster : total ≤ Pmaster := by
    linarith only [hmasterEq, hchart, hD, hradius, hstride, hphysical0]
  have hlate : Pmaster ≤ Plate := le_max_left _ _
  have hscaleLate : Pscale ≤ Plate := (le_max_left _ _).trans (le_max_right _ _)
  have hcoarseLate : coarseTarget ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hxiLate : 2 * (spatialPrimitiveEnvelope Pphysical coarseTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical coarseTarget 0)) + 4
      ≤ Plate :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  intro k
  have hsmReal : (degree k : ℝ) ≤ m := by exact_mod_cast hdegree k
  have hlocalMaster := (htotal k).trans htotalMaster
  have hgainEntry (t : K) : (0 : ℝ) ≤ gainLog t + 32 := by
    have := hg t
    positivity
  have hcoarseSum : gainLog k + 32 ≤ ∑ t, (gainLog t + 32) :=
    Finset.single_le_sum (fun t _ => hgainEntry t) (Finset.mem_univ k)
  refine {
    master_nonneg := hmaster0
    late := hlate
    chart_master := ?_
    dimension_master := ?_
    radius_master := ?_
    scale_late := hscaleLate
    kernel_scale := hkernelScale k
    kernel_master := ⟨hk k, (hkernelPhysical k).trans hphysicalMaster⟩
    stride_master := ⟨hstride, ?_⟩
    detect_master := ⟨hp k, ?_⟩
    ambient_master := le_trans ?_ hphysicalMaster
    u_master := ⟨hu k, ?_⟩
    model_master := ⟨hmodel k, ?_⟩
    slice_model := hslice k
    count_model := hcount k
    rho_master := ⟨hrho k, ?_⟩
    target_master := ⟨ht k, ?_⟩
    gain_master := ⟨hg k, ?_⟩
    coarse_master := ?_
    coarse_lower := hcoarseSum.trans (le_max_left _ _)
    coarse_late := hcoarseLate
    physical_master := ⟨hphysical0, hphysicalMaster⟩
    degree_physical := ?_
    detector_physical := ?_
    variables_physical := ?_
    ambient_physical := ?_
    kernel_physical := hkernelPhysical k
    stride_physical := ?_
    gain_log := le_rfl
    precision := ?_
    xi_late := hxiLate }
  · linarith only [hmasterEq, hD, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hradius, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hstride, hphysical0, htotal0]
  · linarith only [hmasterEq, hchart, hD, hradius, hphysical0, htotal0]
  · linarith only [hlocalMaster, hu k, hmodel k, hrho k, ht k, hg k]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hlocalMaster, hmodel k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hp k, hrho k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, ht k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, hg k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · linarith only [hlocalMaster, hu k, hmodel k, hp k, hrho k, ht k]
  · simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hphysEq, hnX0, hcount0, hstride, hkSum0]
  · simp only [Nat.cast_add, Nat.cast_ofNat]
    linarith only [hphysEq, hsmReal, hnX0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hcount0, hstride, hkSum0]
  · linarith only [hphysEq, hm0, hnX0, hcount0, hkSum0]
  · dsimp only [target]
    linarith only

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem PreparedUniformDegreeDirectScalarBounds.late_mono
    {m s nX nVars Cdetect : ℕ}
    {Pchart Pscale D target Pk Prho Qstride Pmaster Plate Plate' pGain Pphysical
      coarseTarget pRadius u pModel pSlice : ℝ}
    (h : PreparedUniformDegreeDirectScalarBounds m s nX nVars Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical
      coarseTarget pRadius u pModel pSlice)
    (hLate : Plate ≤ Plate') :
    PreparedUniformDegreeDirectScalarBounds m s nX nVars Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate' pGain Pphysical
      coarseTarget pRadius u pModel pSlice := by
  exact { h with
    late := h.late.trans hLate
    scale_late := h.scale_late.trans hLate
    coarse_late := h.coarse_late.trans hLate
    xi_late := h.xi_late.trans hLate }

theorem preparedFiniteScheduleLocalScalarBounds_explicit
    (m degree Cdetect : ℕ) (hdegree : degree ≤ m) (G : Type) [Fintype G]
    (nX count : ℕ) (Pchart D pRadius Qstride Pscale coarseTarget extraLate : ℝ)
    (u pModel pSlice Prho : ℝ)
    (hchart : 0 ≤ Pchart) (hD : 0 ≤ D) (hradius : 0 ≤ pRadius)
    (hu : 0 ≤ u) (hmodel : 0 ≤ pModel) (hstride : 0 ≤ Qstride)
    (hrho : 0 ≤ Prho) (hslice : pSlice ≤ pModel)
    (hcount : (count : ℝ) ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let gainLog := slicedDetectionGainLog degree Cdetect count
      pDetect pDetect (2 * u + 4 * pModel + 7)
    let Pk := scalarKernelLogarithmicBudget (Fin (degree + 1)) G
      (gainLog + pDetect + 4)
    let Pphysical := preparedFiniteScheduleLocalPhysical m nX count Qstride Pk
    let target := gainLog + 40 + coefficientErrorSpatialLog Pphysical
    let Pmaster := preparedFiniteScheduleLocalMaster Pchart D pRadius Qstride
      Pphysical u pModel Prho target gainLog
    let localLate := preparedUniformDegreeDirectLate Pmaster Pscale Pphysical
      coarseTarget extraLate
    Pk ≤ Pscale → gainLog + 32 ≤ coarseTarget →
    ∀ {Plate : ℝ}, localLate ≤ Plate →
      PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
        Pchart Pscale D target Pk Prho Qstride Pmaster Plate gainLog
        Pphysical coarseTarget pRadius u pModel pSlice := by
  intro pDetect gainLog Pk Pphysical target Pmaster localLate hkernel hcoarse Plate hLate
  have h := preparedFiniteScheduleDirectScalarBounds_explicit
    m (fun _ : Unit => degree) (fun _ : Unit => Cdetect) (fun _ => hdegree) G
    nX count Pchart D pRadius Qstride Pscale coarseTarget extraLate
    (fun _ => u) (fun _ => pModel) (fun _ => pSlice) (fun _ => Prho)
    hchart hD hradius (fun _ => hu) (fun _ => hmodel) hstride
    (fun _ => hrho) (fun _ => hslice) (fun _ => hcount)
    (fun _ => hkernel) ()
  have hlocal : PreparedUniformDegreeDirectScalarBounds m degree nX count Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster localLate gainLog
      Pphysical coarseTarget pRadius u pModel pSlice := by
    simpa only [preparedFiniteScheduleDirectMaster, preparedFiniteScheduleDirectCoarse,
      Finset.univ_unique, Finset.sum_singleton, max_eq_right hcoarse,
      Pmaster, Pphysical, target, localLate, gainLog, pDetect, Pk,
      preparedFiniteScheduleLocalPhysical, preparedFiniteScheduleLocalMaster] using h
  exact hlocal.late_mono hLate

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeProductiveSourceModel
namespace OAI


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
variable (u p : ℝ)
local notation "uSource" => u + 2 * p + 1
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog uSource pModel
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))
local notation "Kslice" => Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))
variable (τ forecastCap : ℝ)
local notation "α" => forecastAugmentedUnitThreshold u p Kslice (max 1 Ctail) forecastCap

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

include ν bW μrows in

theorem preparedUniformDegreeGeometryModel
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius uSource pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * uSource + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (0 + 1) * (0 + 3) ≤ Fintype.card G)
    (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hCtail : Ctail ≤ Real.exp p)
    (hForecastCap : 0 ≤ forecastCap) (hForecastCapP : forecastCap ≤ Real.exp p) :
    SharedWidthPreparedCenteredForecastModelInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget ∧
    (normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      (allocatedDetectedKernelCutoff 0 G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect pDetect pDetect (α / 2)) Pphysical coarseTarget)⁻¹ ≤ Real.exp Plate := by
  have hKp : Kslice ≤ Real.exp p := Real.exp_le_exp.mpr hSliceLog
  have hCap := marginalCap_max_one_exp_bound hp hCtail
  have hC : 0 ≤ max 1 Ctail := zero_le_one.trans hCap.1
  have hαlower := (forecastAugmented_separate_source_precision hu hp scalar.model_master.1
    (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2
  have hαone : α / 2 ≤ 1 := by
    have h := (forecastAugmentedUnitThreshold_bounds hu hp
      (Real.exp_nonneg _) hC hKp hCap.2 hForecastCapP).2.1
    linarith only [h]
  have hDirect := preparedUniformDegreeDirectSource_of_geometry_s2
    (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := uSource) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) («α» := α / 2) (τ := τ)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    (Nat.zero_le m) Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain
    Pphysical coarseTarget pRadius scalar geometryAt hRone hRinv hσone hSLate
    hBa hBi hcapacity hαlower hαone
  obtain ⟨⟨geometry⟩, hgainKernel⟩ := geometryAt
  constructor
  · exact preparedUniformDegreeModelChain_s2
      (B := B) (U := U) (basis := basis) (hR := hR) (hσ := hσ) (S := S)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) («uSource» := uSource) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (hb := hb) (o := o) (ν := ν) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget hDirect
      scalar.master_nonneg scalar.late geometry.hdimensions scalar.dimension_master
      scalar.ambient_master scalar.chart_master scalar.stride_master.2 scalar.physical_master.2
      (fun j => (hRinv j).trans (Real.exp_le_exp.mpr scalar.radius_master))
      (fun j => (geometry.hσi j).trans (Real.exp_le_exp.mpr scalar.scale_late))
      hSLate hσone (fun C hC hBound => (geometry.hbudgets C hC hBound).1)
      hu hp hSliceLog hCtail hForecastCap hForecastCapP
  · have hMk := (hgainKernel (α / 2) hαlower).2.1
    have hCoarse : 0 ≤ coarseTarget := by
      linarith only [scalar.gain_master.1, scalar.coarse_lower]
    have hwidth := preparedModularDetector_narrow_width B selection scalar.physical_master.1
      hCoarse (hMk.trans (Real.exp_le_exp.mpr scalar.kernel_physical))
      scalar.detector_physical scalar.variables_physical scalar.ambient_physical
    exact hwidth.2.trans (Real.exp_le_exp.mpr scalar.xi_late)

end Erdos3.VectorPolynomial

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleModelAttachment
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
variable (sourceU : ℝ)
variable (Pdetect : Polynomial ℕ) (pModel pSlice : ℝ) (Vtail : Fin m → ℝ≥0)
local notation "pDetect" => allocatedModelTestLog sourceU pModel
variable (τ : ℝ)

variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]

variable (Q : Fin m → Type) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
variable [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

include ν bW μrows in

theorem preparedFiniteScheduleGeometryModel
    (degree Cdetect : ℕ) (hdegree : degree = 0)
    (hCdetect : Cdetect = sampledSupportedSlicedDetectionConstant 0 Pdetect)
    (Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius : ℝ)
    (scalar : PreparedUniformDegreeDirectScalarBounds m degree nX
      (Fintype.card (LayerSamplerVariables G I n B)) Cdetect
      Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget
      pRadius sourceU pModel pSlice)
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S degree Cdetect nX
      Pchart Pscale D target Pk Prho Qstride pDetect pRadius
      (2 * sourceU + 4 * pModel + 7) pGain)
    (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hσone : ∀ j, σ j ≤ 1)
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val
      (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (0 + 1)) (j.val + 1)).card)
        ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hcapacity : (0 + 1) * (0 + 3) ≤ Fintype.card G) :
    PreparedScheduledModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU) (pModel := pModel) (pSlice := pSlice)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride Pmaster Plate pGain Pphysical coarseTarget := by
  intro u p forecastCap hsource hu hp hslice htail hcap hcapP
  rw [hdegree, hCdetect, hsource] at scalar geometryAt
  rw [hsource]
  exact preparedUniformDegreeGeometryModel
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection) (stride := stride) (N := N)
    (Pdetect := Pdetect) (pModel := pModel) (pSlice := pSlice)
    (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
    (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
    Pchart Pscale D target Pk Prho Qstride Pmaster Plate pGain Pphysical coarseTarget pRadius
    scalar geometryAt hRone hRinv hσone hSLate hBa hBi hcapacity
    hu hp hslice htail hcap hcapP

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFiniteScheduleLocalProductiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

private theorem finiteSchedule_affineLength_density_fin
    (m nX : ℕ) (D P Prho Pk target p Qstride : ℝ) :
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 1)
      (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target (p + 2)
      (((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride)) := by
  simp only [Fintype.card_fin]
  exact Real.exp_le_exp.mpr (allocatedAffineLengthLog_prepared_density m D P Prho Pk target p _)

private theorem finiteSchedule_comparison_eta (target cost : ℝ) :
    Real.exp (-(target + cost + 5)) ≤ Real.exp (-(target + 1 + cost + 4)) := by
  apply Real.exp_le_exp.mpr
  linarith only

theorem exists_preparedFiniteScheduleGeometry (m : ℕ) {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
    {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {Bstruct pnum Qstride : ℝ} (nX : ℕ)
    (pDetect aDetect target : K → ℝ)
    (hm : 0 < m) (hdegree : ∀ s, degree s ≤ m) (hB : 0 ≤ Bstruct) (hnum : pnum ∈ Set.Icc 0 Bstruct)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ s : K, ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin ((degree s) + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : ∀ s, 0 ≤ pDetect s) (ha : ∀ s, 0 ≤ aDetect s) (hQstride : 0 ≤ Qstride)
    (htarget : ∀ s, 0 ≤ target s) :
    PreparedFiniteScheduleGeometryStatement (G := G) m degree Cdetect B
      (Bstruct := Bstruct) (pnum := pnum) (Qstride := Qstride) nX pDetect aDetect target := by
  delta PreparedFiniteScheduleGeometryStatement
  intro Aradius pRadius R D gainLog Pk E Prho Ptail Tmod
  obtain ⟨hRadius, hR, hgeometry⟩ :=
    (Classical.choose_spec (exists_preparedUniformEarlyRadius.{0,0,0,0} m)).2 hB hB
  have hD : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum.1).1
  have hD1 : 1 ≤ D := by
    have hd := (allocatedComparisonDimension_bounds m hnum.1).2.1
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    exact hm1.trans hd
  have hgain (s) : 0 ≤ gainLog s :=
    slicedDetectionGainLog_nonneg (degree s) (Cdetect s) _ (hp s) (hp s) (ha s)
  have hPk (s) : 0 ≤ Pk s := by
    change 0 ≤ scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgain s
    have := hp s
    positivity
  have hcompare (s : K) : 0 ≤ Prho s ∧ 0 ≤ Ptail s ∧
      Nonempty (PreparedUniformDegreeComparison (G := G) B (degree s) D (target s)
        (Pk s) (Prho s) (Ptail s) (pDetect s)) :=
    exists_preparedUniformDegreeComparison_s2 B hm (hdegree s) hnum.1
      hvars hI hn (hblocks s) (hp s) (ha s) (htarget s) hQstride (Cdetect s) nX
  let data := fun s => Classical.choice (hcompare s).2.2
  let t := fun s => (data s).t
  have hTail (s) : 0 ≤ Ptail s := (hcompare s).2.1
  have hdimensions (s : K) : AllocatedComparisonDimensions (G := G) B
      (Fin ((degree s) + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin ((degree s) + 1)) (j.val + 1) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : boundedBooleanJetRows (Fin ((degree s) + 1)) (j.val + 1) → Finset (Fin ((degree s) + 1))))
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ (hdegree s))
      (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
  refine ⟨hRadius, hR, hD, fun s => ⟨hgain s, hPk s, (hcompare s).1, hTail s⟩,
    t, fun s => ⟨(data s).ht, (data s).htone, (data s).htinv⟩, ?_⟩
  intro Qσ hQσ σ Pscale lengthLogs
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hTailScale⟩ :=
    preparedUniformDegreeTolerance_bounds t Ptail (fun s => (data s).ht)
      (fun s => (data s).htone) hTail (fun s => (data s).htinv)
      hQσ (add_nonneg hD hRadius.1)
  have hsum : 0 ≤ ∑ s, Ptail s := Finset.sum_nonneg (fun s _ => hTail s)
  have hDscale : D ≤ Pscale := by
    change D ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hRadius.1, hsum, hQσ]
  have hRadiusScale : pRadius ≤ Pscale := by
    change pRadius ≤ D + pRadius + ∑ s, Ptail s + Qσ
    linarith only [hD, hsum, hQσ]
  have hPkScale (s) : Pk s ≤ Pscale :=
    (prepared_affineProfileToleranceEnvelope_kernel_bound hm canonicalSublevelCutoffLip
      canonicalTransitionLip hD1 (hPk s) (htarget s) (hp s)).trans (hTailScale s)
  have hF (s : K) : 0 ≤ pDetect s + 2 := by linarith only [hp s]
  have hTmod (s) : 0 ≤ Tmod s :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPk s))
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hLengths (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD hPscale (hcompare s).1 (hPk s)
      (htarget s) (hF s) (hTmod s)).2.2.1
  refine ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, ?_⟩
  intro Lmin W Qw Pmin hW hQw hWexp hPmin hLmin J _ U basis Pseed
  have hRi (j) : (R j)⁻¹ ≤ Real.exp Pscale :=
    (hR j).2.2.trans (Real.exp_le_exp.mpr hRadiusScale)
  have hdimZero : AllocatedComparisonDimensions (G := G) B (Fin 1)
      (fun j : Fin m => (boundedBooleanJetRows (Fin 1) (j.val + 1) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B
      (fun j => (Subtype.val : boundedBooleanJetRows (Fin 1) (j.val + 1) → Finset (Fin 1)))
      (by simp) (fun _ => Subtype.val_injective) hnum.1 hvars hI hn
  obtain ⟨S, hlengths, hfloor, hS, hwidth⟩ :=
    exists_preparedUniformDegreeSampler B U basis R (fun _ => σ) lengthLogs
      hdimZero hDscale (fun j => (hR j).1) (fun _ => hσ)
      hRi (fun _ => hσinv) hLengths hPmin hLmin hW hQw hWexp
  refine ⟨S, hfloor, hS, hwidth, ?_⟩
  intro s
  let rowSets := fun j : Fin m => boundedBooleanJetRows (Fin ((degree s) + 1)) (j.val + 1)
  let : ∀ j : Fin m, Nonempty (rowSets j) := fun j =>
    ⟨⟨∅, (mem_boundedBooleanJetRows (j.val + 1) ∅).mpr (by simp)⟩⟩
  obtain ⟨hrone, _, hT, hsource, hradius, hbudgets⟩ :=
    hgeometry (G := G) B rowSets
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ (hdegree s))
      (hvars.trans hnum.2) (fun j => (hI j).trans hnum.2) (fun j => (hn j).trans hnum.2)
  have hcount (j : Fin m) : (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp Pscale :=
    ((add_le_add ((hdimensions s).coefficients j) (le_refl (1 : ℝ))).trans
      (Real.add_one_le_exp D)).trans (Real.exp_le_exp.mpr hDscale)
  refine ⟨?_, ?_⟩
  · refine allocatedEarlyNativeSourceGeometryGeneral_of_fields B U basis S
      Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) (Real.toNNReal (Real.exp pRadius))
      hPscale (fun j => (hR j).2.1.trans (Real.one_le_exp hPscale))
      hRi (fun _ => hσinv) hcount (hdimensions s) (hPk s) (hcompare s).1 (htarget s) ?_
      (Real.exp (-(E s))) (Real.exp_pos _).le ?_ (data s).ρ (data s).t (data s).htone
      ((data s).hs)
      (data s).hρ (data s).hρ1 (data s).hρlog (fun _ => hσt s)
      (allocatedIdealCoverSupport (G := G) B rowSets) hT hsource
      (allocatedProductIdealSiteRadius (G := G) B rowSets) hrone hradius hbudgets
      (fun j => (hR j).2.2.trans (Real.le_coe_toNNReal _))
    · exact (finiteSchedule_affineLength_density_fin m nX D Pscale (Prho s) (Pk s)
        (target s) (pDetect s) Qstride).trans (hlengths s)
    · exact finiteSchedule_comparison_eta (target s) (D * ((m * 2 ^ (m + 1) : ℕ) * Pk s))
  · intro α hα gain
    have hcutoff := slicedDetection_kernel_cutoff_bound_s2 (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables G I n B)) G (hp s) (hp s) (ha s) hα
    exact ⟨slicedDetectionGain_lower (degree s) (Cdetect s) _ hα, hcutoff,
      allocatedAffineLength_kernel_ready hm hD hPscale (hcompare s).1 (hPk s)
        (htarget s) (hF s) (hTmod s) hcutoff (hlengths s)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem exists_preparedFiniteScheduleLocalProductiveSource_s2_oai
    {m nX M : ℕ} {X₀ J₀ : Type} (prep : RankPreparationFamily X₀ J₀ m)
    [∀ j : Fin m, DecidableEq (RankPreparationLayer.Coord (prep j))]
    (U : ∀ j, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j → ℝ))
    (b : ∀ j, Basis (Fin ((preparedSamplerTransverse prep) j)) ℝ (euclideanSubspace (U j))ᗮ)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (Vtail : Fin m → ℝ≥0)

    (Q : Fin m → Type) [∀ j, Fintype (Q j)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis ((PreparedSamplerContinuous prep) j) ℝ (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (prep j)) j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    [CompactSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    [BorelSpace (CoefficientTorus (K := Fin (0 + 1)) U)]
    (μrows : Measure (CoefficientTorus (K := Fin (0 + 1)) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]
    [MeasurableSpace (SiteTorus (Finset (Fin (0 + 1))) U)]
    [BorelSpace (SiteTorus (Finset (Fin (0 + 1))) U)]

    {K : Type} [Fintype K] (degree Cdetect : K → ℕ) (kModel : K)
    (hdegree : ∀ k, degree k ≤ m) (hdegreeZero : degree kModel = 0)
    (hCzero : Cdetect kModel = sampledSupportedSlicedDetectionConstant 0 Pdetect)
    (Bstruct Qstride u p forecastCap : ℝ)
    (sourceU modelLog sliceLog : K → ℝ)
    (hModelSource : sourceU kModel = u + 2 * p + 1)
    (Qσ Qw Pmin requestedCoarse gainLog gain Vlog : ℝ)
    (Lmin Qgood : ℕ)
    (hm : 0 < m) (hnX : 0 < nX)
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hB : 0 ≤ Bstruct) (hu : 0 ≤ u) (hp : 0 ≤ p)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) : ℝ) ≤ Real.exp (modelLog k))
    (hQstride : 0 ≤ Qstride)
    (hQσ : 0 ≤ Qσ) (hQw : 0 ≤ Qw) (hPmin : 0 ≤ Pmin)
    (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin)
    (hg : 0 ≤ gainLog) (hVlog : 0 ≤ Vlog)
    (hQgood : 1 ≤ Qgood) (hQexp : (Qgood : ℝ) ≤ Real.exp Vlog)
    (hgain : Real.exp (-gainLog) ≤ gain)
    (hnChart : (nX : ℝ) ≤ Bstruct) (hgChart : gainLog ≤ Bstruct) :
    let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M (modularInitialBlockCount m (nX + m * M))
    let R : Fin m → ℝ := fun _ => allocatedCommonProductRadius m Bstruct Bstruct
    let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
    let D := allocatedComparisonDimension m pnum
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun s : K => slicedDetectionGainLog (degree s) (Cdetect s)
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) (pDetect s) (pDetect s) (aDetect s)
    let Pk := fun s : K => scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
      (detectionGain s + pDetect s + 4)
    let Pphysical := fun k : K => preparedFiniteScheduleLocalPhysical m nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))))) Qstride (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
    let Prho := fun s : K => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
    let Ptail := fun s : K => affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
    let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
    let lengthLogs := fun s : K => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
      (target s) (pDetect s + 2) (Tmod s)
    let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
    let W := physicalBadProductGap ((modularInitialBlockCount m (nX + m * M)) * (nX + m * M)) (gainLog + 8) Vlog Qgood
    let Pmaster := fun k : K => preparedFiniteScheduleLocalMaster Bstruct D pRadius Qstride
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain requestedCoarse
    let Plate := ∑ k : K, preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    pnum ≤ Bstruct →
    W ≤ Real.exp Qw →
    sliceLog kModel * Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) ≤ p →
    (4 * ∏ j, earlyConstantDensityCap (Fintype.card ((PreparedSamplerContinuous prep) j)) ((preparedSamplerTransverse prep) j) (R j) (Vtail j)) ≤ Real.exp p →
    0 ≤ forecastCap → forecastCap ≤ Real.exp p →
    ∃ (hR : ∀ j, 0 < R j) (σ : ℝ) (hσ : 0 < σ)
      (S : LayerSamplerScale («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) («I» := (PreparedSamplerContinuous prep)) («n» := (preparedSamplerTransverse prep)) («J» := (fun j : Fin m => RankPreparationLayer.Coord (prep j))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R (fun _ => σ)),
      0 ≤ pRadius ∧ (∀ j, R j ≤ 1 ∧ (R j)⁻¹ ≤ Real.exp pRadius) ∧
      σ ≤ 1 ∧ σ ≤ Real.exp (-Qσ) ∧ σ⁻¹ ≤ Real.exp Pscale ∧
      Lmin ≤ S.value ∧ (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog Pseed Qw) ∧
      (∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1))) ∧
      (∀ s : K, PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S (degree s) (Cdetect s) nX
        Bstruct Pscale D (target s) (Pk s) (Prho s) Qstride (pDetect s) pRadius (aDetect s) (detectionGain s)) ∧
      (∀ k, PreparedUniformDegreeDirectScalarBounds m (degree k) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k) (sliceLog k)) ∧
      (∀ k, Cdetect k = sampledSupportedSlicedDetectionConstant (degree k) Pdetect →
        PreparedScheduledDirectSourceAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, degree k = 0 →
        Cdetect k = sampledSupportedSlicedDetectionConstant 0 Pdetect →
        PreparedScheduledModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      (∀ k, Cdetect k = sampledSupportedSlicedDetectionConstant (degree k) Pdetect →
        PreparedScheduledDegreeModelAvailability
          (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
          (U := U) (basis := b) (S := S) (hR := hR) (hσ := fun _ => hσ)
          (selection := enlargedPreparedCommonCanonicalSelection m
            (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
          (stride := stride) (N := N) (Pdetect := Pdetect)
          (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
          (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
          Bstruct Qstride (Pmaster k) Plate (detectionGain k) (Pphysical k) coarseTarget) ∧
      PreparedUniformDegreeProductiveSourceConclusion
        (m := m) (nX := nX) (M := M) (prep := prep) (U := U) (b := b) (S := S)
        (hR := hR) (hσ := fun _ => hσ) (stride := stride) (N := N)
        (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
        (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
        (hb := hb) (o := o) (bW := bW) (μ := μ)
        Bstruct Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget
        pRadius Pscale Pseed Qw gainLog gain Vlog Qgood := by
  intro pnum R pRadius D pDetect aDetect detectionGain Pk Pphysical target E Prho Ptail Pscale Tmod
    lengthLogs Pseed W Pmaster coarseTarget Plate τ hnum hWexp
    hSliceLog hCtail hForecastCap hForecastCapP
  have hpnum : 0 ≤ pnum := Nat.cast_nonneg _
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions prep (modularInitialBlockCount m (nX + m * M)) hCoord
  have hblocks (s : K) (a : LayerSamplerAxis (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)) :
      (boundedBooleanJetRows (Fin (degree s + 1)) (a.1.val + 1)).card ≤ Fintype.card ((EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) a) := by
    calc
      _ = Fintype.card (BoundedBooleanJet (Fin (degree s + 1)) (a.1.val + 1)) :=
        (Fintype.card_coe _).symm.trans (Fintype.card_congr (boundedBooleanJetRowsEquiv _ _))
      _ ≤ _ := enlargedPreparedCommonSamplerBlock_jets prep (modularInitialBlockCount m (nX + m * M)) (degree s) (hdegree s) a
  have hpDetect (k) : 0 ≤ pDetect k := by
    dsimp only [pDetect, allocatedModelTestLog]
    linarith only [hsourceU k, hmodelLog k]
  have haDetect (k) : 0 ≤ aDetect k := by
    dsimp only [aDetect]
    linarith only [hsourceU k, hmodelLog k]
  have hgainDetect (k) : 0 ≤ detectionGain k :=
    slicedDetectionGainLog_nonneg (degree k) (Cdetect k) _ (hpDetect k) (hpDetect k) (haDetect k)
  have hkernel (k) : 0 ≤ Pk k := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    have := hgainDetect k
    have := hpDetect k
    positivity
  have hphysical (k) : 0 ≤ Pphysical k := by
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    have := hkernel k
    positivity
  have hphysicalX (k) : (nX : ℝ) ≤ Pphysical k := by
    dsimp only [Pphysical, preparedFiniteScheduleLocalPhysical]
    have hcount : (0 : ℝ) ≤ Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) := Nat.cast_nonneg _
    have hm2 : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith only [hcount, hm2, hkernel k, hQstride]
  have htarget (k) : 0 ≤ target k := by
    have he := coefficientErrorSpatialLog_nonneg (hphysical k)
    dsimp only [target]
    linarith only [hgainDetect k, he]
  have hactual := exists_preparedFiniteScheduleGeometry m degree Cdetect (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) nX pDetect aDetect target
    hm hdegree hB ⟨hpnum, hnum⟩ (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j))
    (fun j => Nat.cast_le.mpr (hn j)) hblocks hpDetect haDetect hQstride htarget
  obtain ⟨hpRadius, hR, hD, hlogs, t, ht, hsamplers⟩ := hactual
  obtain ⟨hσ, hσone, hσt, hσexp, hσinv, hPscale, hDscale, hPkScale, hscales⟩ := hsamplers hQσ
  have hW : 1 ≤ W := (physicalBadProductGap_budget _
    (show 0 ≤ gainLog + 8 by linarith only [hg]) hVlog Qgood hQgood hQexp).1
  obtain ⟨S, hFloor, hS, hgap, hGeometryAll⟩ := hscales Lmin hW hQw hWexp hPmin hLmin U b
  let σ := preparedUniformDegreeTolerance t Qσ
  have hF (s) : 0 ≤ pDetect s + 2 := by linarith only [hpDetect s]
  have hTmod (s) : 0 ≤ Tmod s :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hlogs s).2.1)
      (mul_nonneg (Nat.cast_nonneg _) hQstride)
  have hLengths (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD hPscale (hlogs s).2.2.1 (hlogs s).2.1
      (htarget s) (hF s) (hTmod s)).2.2.1
  have hPseed : 0 ≤ Pseed := allocatedScaleLog_nonneg
    (add_nonneg (add_nonneg (add_nonneg hPscale (Finset.sum_nonneg (fun s _ => hLengths s))) hPmin)
      (by norm_num))
  have hmaster (k) : 0 ≤ Pmaster k := by
    dsimp only [Pmaster, preparedFiniteScheduleLocalMaster]
    have hr := (hlogs k).2.2.1
    have ht := htarget k
    have hph := hphysical k
    have hu := hsourceU k
    have hm := hmodelLog k
    have hd := hpDetect k
    have hg := hgainDetect k
    change 0 ≤ Bstruct + D + pRadius + Qstride + Pphysical k +
      (sourceU k + modelLog k + pDetect k + Prho k + target k + detectionGain k + 32)
    linarith only [hB, hD, hpRadius.1, hQstride, hr, ht, hph, hu, hm, hd, hg]
  have hLate (k) : preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget (allocatedWitnessScaleLog Pseed Qw) ≤ Plate :=
    Finset.single_le_sum
      (f := fun t : K => preparedUniformDegreeDirectLate (Pmaster t) Pscale
        (Pphysical t) coarseTarget (allocatedWitnessScaleLog Pseed Qw))
      (fun t _ => (hmaster t).trans (le_max_left _ _)) (Finset.mem_univ k)
  have hcoarse (k) : detectionGain k + 32 ≤ coarseTarget := by
    exact (Finset.single_le_sum (f := fun t : K => detectionGain t + 32)
      (fun t _ => by linarith only [hgainDetect t])
      (Finset.mem_univ k)).trans (le_max_left _ _)
  have scalarAll (k) := preparedFiniteScheduleLocalScalarBounds_explicit
    m (degree k) (Cdetect k) (hdegree k)
    (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    nX (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
    Bstruct D pRadius Qstride Pscale coarseTarget (allocatedWitnessScaleLog Pseed Qw)
    (sourceU k) (modelLog k) (sliceLog k) (Prho k)
    hB hD hpRadius.1 (hsourceU k) (hmodelLog k) hQstride (hlogs k).2.2.1
    (hsliceModel k) (hcountModel k) (hPkScale k) (hcoarse k) (hLate k)
  have scalar : PreparedUniformDegreeDirectScalarBounds m 0 nX
      (Fintype.card (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
      (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride (Pmaster kModel) Plate
      (detectionGain kModel) (Pphysical kModel) coarseTarget pRadius (u + 2 * p + 1)
      (modelLog kModel) (sliceLog kModel) := by
    have hstage : PreparedUniformDegreeDirectScalarBounds m (degree kModel) nX
        (Fintype.card (LayerSamplerVariables
          (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
          (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep)
          (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))))
        (Cdetect kModel) Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel)
        Qstride (Pmaster kModel) Plate (detectionGain kModel) (Pphysical kModel) coarseTarget pRadius
        (sourceU kModel) (modelLog kModel) (sliceLog kModel) := scalarAll kModel
    rw [hdegreeZero, hCzero, hModelSource] at hstage
    exact hstage
  have hGeometryZero : PreparedUniformDegreeGeometryAt («G» := (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S 0
      (sampledSupportedSlicedDetectionConstant 0 Pdetect) nX
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride
      (allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel)) pRadius
      (2 * (u + 2 * p + 1) + 4 * modelLog kModel + 7) (detectionGain kModel) := by
    have hstage : PreparedUniformDegreeGeometryAt
        (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
        U b S (degree kModel) (Cdetect kModel) nX
        Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride
        (pDetect kModel) pRadius (aDetect kModel) (detectionGain kModel) := hGeometryAll kModel
    have hpd : pDetect kModel = allocatedModelTestLog (u + 2 * p + 1) (modelLog kModel) := by
      change allocatedModelTestLog (sourceU kModel) (modelLog kModel) = _
      rw [hModelSource]
    have had : aDetect kModel = 2 * (u + 2 * p + 1) + 4 * modelLog kModel + 7 := by
      change 2 * sourceU kModel + 4 * modelLog kModel + 7 = _
      rw [hModelSource]
    rw [hdegreeZero, hCzero, hpd, had] at hstage
    exact hstage
  have hWitnessLate : allocatedWitnessScaleLog Pseed Qw ≤ Plate :=
    (preparedUniformDegreeDirectLate_extra (Pmaster kModel) Pscale
      (Pphysical kModel) coarseTarget (allocatedWitnessScaleLog Pseed Qw)).trans (hLate kModel)
  have hGainMaster : gainLog + (nX : ℝ) + 8 ≤ Pmaster kModel := by
    have hr := (hlogs kModel).2.2.1
    change gainLog + (nX : ℝ) + 8 ≤ Bstruct + D + pRadius + Qstride + Pphysical kModel +
      (sourceU kModel + modelLog kModel + pDetect kModel + Prho kModel + target kModel + detectionGain kModel + 32)
    linarith only [hgChart, hD, hpRadius.1, hQstride, hphysicalX kModel,
      hsourceU kModel, hmodelLog kModel, hpDetect kModel, hr, htarget kModel, hgainDetect kModel]
  refine ⟨(fun j => (hR j).1), σ, hσ, S, hpRadius.1,
    (fun j => (hR j).2), hσone, hσexp, hσinv, hFloor, hS, hgap, hGeometryAll, scalarAll, ?_, ?_, ?_, ?_⟩
  · intro k hconstant
    exact preparedFiniteScheduleGeometryDirectSource_s2
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
      (Cdetect k) hconstant (hdegree k)
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
  · intro k hzero hconstant
    exact preparedFiniteScheduleGeometryModel
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
      (degree k) (Cdetect k) hzero hconstant
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) 0 (Nat.zero_le m))
  · intro k hconstant
    exact preparedFiniteScheduleDegreeGeometryModel_s2
      (B := EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))
      (U := U) (basis := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (selection := enlargedPreparedCommonCanonicalSelection m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
      (stride := stride) (N := N) (Pdetect := Pdetect) (sourceU := sourceU k)
      (pModel := modelLog k) (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ)
      (Cdetect k) hconstant (hdegree k)
      Bstruct Pscale D (target k) (Pk k) (Prho k) Qstride (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (scalarAll k) (hGeometryAll k)
      (fun j => (hR j).2.1) (fun j => (hR j).2.2) (fun _ => hσone)
      (hS.trans (Real.exp_le_exp.mpr hWitnessLate))
      (fun j i => enlargedPreparedCommonSamplerBlock_positiveModerate prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (fun j i => enlargedPreparedCommonSamplerBlock_uniform prep
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k) ⟨j, Sum.inr i⟩)
      (enlargedPreparedCommonKernel_analytic_capacity m
        (modularInitialBlockCount m (nX + m * M)) (degree k) (hdegree k))
  · exact preparedUniformDegreeProductiveSource_s2
      (prep := prep) (U := U) (b := b) (S := S) (hR := fun j => (hR j).1) (hσ := fun _ => hσ)
      (stride := stride) (N := N) (Pdetect := Pdetect) (pModel := modelLog kModel) (pSlice := sliceLog kModel)
      (Vtail := Vtail) (τ := τ) (u := u) (p := p) (forecastCap := forecastCap)
      (Q := Q) (hb := hb) (o := o) (bW := bW) (ν := ν) (μ := μ) (μrows := μrows)
      Bstruct Pscale D (target kModel) (Pk kModel) (Prho kModel) Qstride (Pmaster kModel) Plate (detectionGain kModel)
      (Pphysical kModel) coarseTarget pRadius scalar hGeometryZero
      (fun j => (hR j).2.1) (fun j => (hR j).2.2)
      hu hp hSliceLog hCtail hForecastCap hForecastCapP
      Qgood hm hnX hCoord hpRadius.1 hPseed hQw hVlog hg hQgood hQexp
      hWitnessLate hgain hB hnChart hgChart hGainMaster rfl hS hgap

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleLocalProductiveSource_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedFiniteScheduleLocalProductiveSource_s2_oai
