-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeComparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:55:32.229049+00:00
-- url     : https://prove2.me/submissions/f6e0e07f-5401-4dde-bf16-595099333969

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B261
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_bounded_source_s2
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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open scoped BigOperators

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

 theorem allocatedAffineScale_lower (D P Prho Pk target F T : ℝ) :
    Real.exp (allocatedAffineLengthLog m D P Prho Pk target F T) ≤
      ((allocatedAffineScale (G := G) B U basis hR hσ D P Prho Pk target F T).value : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.mpr
    (selectedLayerSamplerScale_bounds B U basis R σ hR hσ _).1)

 theorem allocatedAffineScale_upper {D P Prho Pk target F T : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hr : 0 ≤ Prho) (hk : 0 ≤ Pk) (ht : 0 ≤ target)
    (hF : 0 ≤ F) (hT : 0 ≤ T)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P) :
    ((allocatedAffineScale (G := G) B U basis hR hσ D P Prho Pk target F T).value : ℝ) ≤
      Real.exp (allocatedScaleLog (D + P + allocatedAffineLengthLog m D P Prho Pk target F T + 1)) := by
  let L := allocatedAffineLengthLog m D P Prho Pk target F T
  let Q := D + P + L + 1
  have hD := hdim.nonneg
  have hL := (allocatedAffineLengthLog_bounds m hD hP hr hk ht hF hT).2.2.1
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hDQ : D ≤ Q := by dsimp [Q]; linarith
  have hPQ : P ≤ Q := by dsimp [Q]; linarith
  have hLQ : L + 1 ≤ Q := by dsimp [Q]; linarith
  apply selectedLayerSamplerScale_exp_bound B U basis R σ hR hσ _ hQ
    (hdim.degree.trans hDQ) (fun j => (hdim.integer_axes B j).trans hDQ)
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hPQ))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hPQ))
    (fun j => (hdim.coefficients j).trans hDQ)
  · exact (hdim.profile.trans hDQ).trans (by linarith [Real.add_one_le_exp Q])
  · exact (natCeil_le_exp_succ_of_le hL le_rfl).trans (Real.exp_le_exp.mpr hLQ)

end Erdos3.VectorPolynomial

end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EarlyAllocatedAffineL1Scales
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_l1_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ target Pk F Tmod D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (htarget : 0 ≤ target) (hPk : 0 ≤ Pk) (hF : 0 ≤ F) (hTmod : 0 ≤ Tmod)
    (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {p : ℝ}, 0 ≤ p → (∀ j, (R j)⁻¹ ≤ Real.exp p) →
        let P := p + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) := by
  intro maskLog E η Prho Ptail K
  have hD := hdim.nonneg
  have hm : 0 ≤ maskLog := by dsimp [maskLog]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcoeff : 0 ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold affineProfileCoefficientEnvelope; positivity
  have hinput : 0 ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F :=
    jointAffineSourceEnvelope_nonneg hD hcoeff (by positivity) hF
  have hr : 0 ≤ Prho := by dsimp [Prho]; positivity
  have htail : 0 ≤ Ptail := by
    dsimp [Ptail, affineProfileToleranceEnvelope]
    positivity
  obtain ⟨ρ, hρ, _, t, ht, htone, htlog, _, hs⟩ :=
    exists_early_allocated_affine_bounded_source_s2.{uJ,uQ} B rows hrows hcard ψ hψ hrange hzero hone
      A T hLip hTransition block hblock hdim hδ hδone htarget hm hF hδF
  refine ⟨hr, htail, ρ, ?_, t, ht, htone, htlog, hs, ?_⟩
  · intro partition
    refine ⟨(hρ partition).1, (hρ partition).2.1, ?_⟩
    have hlow := (hρ partition).2.2
    rw [Real.exp_neg] at hlow
    exact (inv_le_comm₀ (show 0 < (ρ partition : ℝ) from (hρ partition).1) (Real.exp_pos Prho)).mpr hlow
  · intro J _ U basis R hR p hp hRi P
    have hP : 0 ≤ P := add_nonneg hp htail
    have hRbound (j) : (R j)⁻¹ ≤ Real.exp P :=
      (hRi j).trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right htail))
    have htbound : t⁻¹ ≤ Real.exp P :=
      htlog.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hp))
    let S := allocatedAffineScale (G := G) B U basis hR (fun _ => ht) D P Prho Pk target F Tmod
    refine ⟨S, hRbound, fun _ => htbound,
      allocatedAffineScale_lower B U basis hR (fun _ => ht) D P Prho Pk target F Tmod, ?_⟩
    exact (allocatedAffineScale_upper B U basis hR (fun _ => ht) hdim hP hr hPk htarget hF hTmod
      hRbound (fun _ => htbound)).trans (Real.exp_le_exp.mpr
        ((Classical.choose_spec (exists_allocatedAffineScaleLog_bound m)).2
          D P Prho Pk target F Tmod hD hP hr hPk htarget hF hTmod))

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

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {s : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin (s + 1)))
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_canonical_slice_scales
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {target D p q a Qstride : ℝ} (hdegree : 0 < m)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) O D)
    (htarget : 0 ≤ target) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hQstride : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) p q a
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
    let F := p + 2
    let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let δ := Real.exp (-(p + 1))
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {pRadius : ℝ}, 0 ≤ pRadius → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
        let P := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) ∧
          ∀ α : ℝ, Real.exp (-a) ≤ α →
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
              (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
                Real.exp (-((q + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro gainLog Pk F Tmod δ maskLog E η Prho Ptail K
  have hgain0 : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect _ hp hq ha
  have hPk : 0 ≤ Pk := by
    dsimp only [Pk]
    rw [scalarKernelLogarithmicBudget_eq]
    positivity
  have hF : 0 ≤ F := by dsimp only [F]; linarith
  have hTmod : 0 ≤ Tmod := by dsimp only [Tmod]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hδone : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hδF : (δ / 2)⁻¹ ≤ Real.exp F := by
    dsimp only [δ, F]
    simp only [Real.exp_neg, div_eq_mul_inv, mul_inv_rev, inv_inv]
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp (p + 1) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm.trans (congrArg Real.exp (by ring))
  obtain ⟨hPrho, hPtail, ρ, hρ, t, ht, htone, htlog, hs, hscales⟩ :=
    exists_early_allocated_affine_l1_scales.{uJ,uQ} B rows hrows hcard ψ hψ hrange hzero hone A T hLip hTransition
      block hblock hdim hδ hδone htarget hPk hF hTmod hδF
  refine ⟨hPrho, hPtail, ρ, hρ, t, ht, htone, htlog, hs, ?_⟩
  intro J _ U basis R hR pRadius hpRadius hRi P
  obtain ⟨S, hRiP, hσP, hlength, hupper⟩ := hscales U basis R hR hpRadius hRi
  refine ⟨S, hRiP, hσP, hlength, hupper, ?_⟩
  intro α hα
  have hcutoff := slicedDetection_kernel_cutoff_bound_s2 s Cdetect
    (Fintype.card (LayerSamplerVariables G I n B)) G hp hq ha hα
  exact allocatedAffineLength_kernel_ready hdegree hdim.nonneg (add_nonneg hpRadius hPtail)
    hPrho hPk htarget hF hTmod hcutoff hlength

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

theorem canonicalSublevelCutoff_spec :
    ContDiff ℝ ∞ canonicalSublevelCutoff ∧
    (∀ t, canonicalSublevelCutoff t ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t, |t| ≤ 1 → canonicalSublevelCutoff t = 0) ∧
    (∀ t, 2 ≤ |t| → canonicalSublevelCutoff t = 1) ∧
    LipschitzWith canonicalSublevelCutoffLip canonicalSublevelCutoff :=
  Classical.choose_spec (Classical.choose_spec exists_smooth_sublevel_cutoff).2

theorem canonicalTransitionLip_spec :
    LipschitzWith canonicalTransitionLip Real.smoothTransition :=
  (Classical.choose_spec exists_smoothTransition_lipschitz).2

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {s : ℕ}
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin (s + 1)))

theorem exists_initialized_early_canonical_slice_scales
    (hrows : ∀ j, Function.Injective (rows j))
    (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)
    (hblocks : ∀ a : LayerSamplerAxis I n, Fintype.card (O a.1) ≤ Fintype.card (B a))
    {target D p q a Qstride : ℝ} (hdegree : 0 < m)
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) O D)
    (htarget : 0 ≤ target) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hQstride : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) p q a
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
    let F := p + 2
    let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let δ := Real.exp (-(p + 1))
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {pRadius : ℝ}, 0 ≤ pRadius → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
        let P := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) ∧
          ∀ α : ℝ, Real.exp (-a) ≤ α →
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
              (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
                Real.exp (-((q + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  let block (a : LayerSamplerAxis I n) : O a.1 ↪ B a :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hblocks a))
  obtain ⟨hsmooth, hrange, hzero, hone, hLip⟩ := canonicalSublevelCutoff_spec
  exact exists_early_allocated_canonical_slice_scales.{uJ,uQ} B rows hrows hcard
    canonicalSublevelCutoff hsmooth hrange hzero hone
    canonicalSublevelCutoffLip canonicalTransitionLip hLip canonicalTransitionLip_spec
    (fun a => block a) (fun a => (block a).injective) hdegree hdim
    htarget hp hq ha hQstride Cdetect nX

attribute [local instance 2000] fullBooleanRowSetFintype
local notation "fullRowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
local notation "fullRowTypes" => (fun j : Fin m => (fullRowSets j : Type))
local notation "fullRows" => (fun j : Fin m => (Subtype.val : fullRowSets j → Finset (Fin (s + 1))))

theorem exists_primitive_early_canonical_slice_scales
    {target pnum p q a Qstride : ℝ} (hdegree : 0 < m) (hs : s ≤ m)
    (hpnum : 0 ≤ pnum)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum)
    (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (htarget : 0 ≤ target) (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 0 ≤ a) (hQstride : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let D := allocatedComparisonDimension m pnum
    let gainLog := slicedDetectionGainLog s Cdetect (Fintype.card (LayerSamplerVariables G I n B)) p q a
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
    let F := p + 2
    let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
    let δ := Real.exp (-(p + 1))
    let maskLog := D * ((m * 2 ^ (m + 1) : ℕ) * Pk)
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
    let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ partition, 0 < ρ partition ∧ ρ partition ≤ 1 ∧ (ρ partition : ℝ)⁻¹ ≤ Real.exp Prho) ∧
    ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t⁻¹ ≤ Real.exp Ptail ∧
      AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B fullRows δ η ρ t htone ∧
      ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        (R : Fin m → ℝ), (∀ j, 0 < R j) →
        ∀ {pRadius : ℝ}, 0 ≤ pRadius → (∀ j, (R j)⁻¹ ≤ Real.exp pRadius) →
        let P := pRadius + Ptail
        ∃ S : LayerSamplerScale (G := G) B U basis R (fun _ => t),
          (∀ j, (R j)⁻¹ ≤ Real.exp P) ∧ (∀ j : Fin m, ((fun _ => t) j)⁻¹ ≤ Real.exp P) ∧
          Real.exp (allocatedAffineLengthLog m D P Prho Pk target F Tmod) ≤ S.value ∧
          (S.value : ℝ) ≤ Real.exp ((D + P + Prho + Pk + target + F + Tmod + K) ^ K) ∧
          ∀ α : ℝ, Real.exp (-a) ≤ α →
            scalarKernelCutoff (Fin (s + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
              (((Real.exp (-((5 * p + 20) * Fintype.card (LayerSamplerVariables G I n B) + p + 2)) * (α / 2)) *
                Real.exp (-((q + Cdetect) ^ Cdetect)) ^ (2 ^ (s + 1))) / 2) ≤ S.value := by
  intro D
  let (j : Fin m) : Nonempty (fullRowTypes j) :=
    ⟨⟨∅, (mem_boundedBooleanJetRows _ _).mpr (by simp)⟩⟩
  have hinj : ∀ j, Function.Injective (fullRows j) := fun _ => Subtype.val_injective
  have hcard : ∀ j (a : fullRowTypes j), (fullRows j a).card ≤ j.val + 1 :=
    fun j a => (mem_boundedBooleanJetRows _ _).mp a.property
  have hdim : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) fullRowTypes D :=
    allocatedComparisonDimensions_of_primitive B fullRows
      (by simpa only [Fintype.card_fin] using Nat.succ_le_succ hs) hinj hpnum hK hI hn
  have hblocks' : ∀ b : LayerSamplerAxis I n,
      Fintype.card (fullRowTypes b.1) ≤ Fintype.card (B b) := by
    intro b
    simpa only [Fintype.card_coe] using hblocks b
  exact exists_initialized_early_canonical_slice_scales.{uJ,uQ} B fullRows hinj hcard hblocks'
    hdegree hdim htarget hp hq ha hQstride Cdetect nX

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeDirectMasterBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreeComparison_s2_oai
    {m s : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {pnum pDetect aDetect target Qstride : ℝ} (hm : 0 < m) (hs : s ≤ m)
    (hnum : 0 ≤ pnum)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ pnum) (hn : ∀ j, (n j : ℝ) ≤ pnum)
    (hblocks : ∀ b : LayerSamplerAxis I n,
      (boundedBooleanJetRows (Fin (s + 1)) (b.1.val + 1)).card ≤ Fintype.card (B b))
    (hp : 0 ≤ pDetect) (ha : 0 ≤ aDetect) (htarget : 0 ≤ target) (hQ : 0 ≤ Qstride)
    (Cdetect nX : ℕ) :
    let D := allocatedComparisonDimension m pnum
    let gainLog := slicedDetectionGainLog s Cdetect
      (Fintype.card (LayerSamplerVariables G I n B)) pDetect pDetect aDetect
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
    let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ)
      (canonicalTransitionLip : ℝ) E (pDetect + 2) + 2
    let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E (pDetect + 2)
    0 ≤ Prho ∧ 0 ≤ Ptail ∧
      Nonempty (PreparedUniformDegreeComparison (G := G) B s D target Pk Prho Ptail pDetect) := by
  intro D gainLog Pk E Prho Ptail
  obtain ⟨hRho, hTail, ρ, hρ, t, ht, htone, htinv, hcomparison, _⟩ :=
    exists_primitive_early_canonical_slice_scales.{0,0} B hm hs hnum
      hvars hI hn hblocks htarget hp hp ha hQ Cdetect nX
  refine ⟨hRho, hTail, ⟨{
    ρ := ρ
    hρ := fun partition => (hρ partition).1
    hρ1 := fun partition => (hρ partition).2.1
    hρlog := fun partition => (hρ partition).2.2
    t := t
    ht := ht
    htone := htone
    htinv := htinv
    hs := ?_ }⟩⟩
  exact @hcomparison

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeComparison_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_preparedUniformDegreeComparison_s2_oai
