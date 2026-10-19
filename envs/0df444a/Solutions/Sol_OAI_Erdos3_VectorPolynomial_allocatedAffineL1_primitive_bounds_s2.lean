-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:57:27.857801+00:00
-- url     : https://prove2.me/submissions/229b6ffa-84e7-4d31-8a65-4af26e59d1e1

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.JointPivotProfileBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem affineProductProfileLip_le_exp (I : Type*) [Fintype I]
    {δ : ℝ≥0} {t : ℝ} (hi : (δ : ℝ)⁻¹ ≤ Real.exp t) :
    (affineProductProfileLip I δ : ℝ) ≤ Real.exp (affineProfileLogBound (Fintype.card I) t) := by
  have hn : (Fintype.card I : ℝ) ≤ Real.exp (Fintype.card I : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card I : ℝ)]
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) := by
    linarith [Real.add_one_le_exp (probabilityProfileLipschitz : ℝ)]
  simp only [affineProductProfileLip, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_inv]
  calc
    _ ≤ Real.exp (Fintype.card I : ℝ) * Real.exp (probabilityProfileLipschitz : ℝ) *
        (Real.exp t)^(Fintype.card I + 1) := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [affineProfileLogBound, Nat.cast_add, Nat.cast_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem kernelGeometryLog_bounds (q n j k d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ kernelGeometryLog q n j k d p ∧ p ≤ kernelGeometryLog q n j k d p ∧
    kernelInverseLog q n j d p ≤ kernelGeometryLog q n j k d p ∧
    (j : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p ∧
    (k : ℝ) + (q : ℝ) * (d + 1) ≤ kernelGeometryLog q n j k d p := by
  have hi : 0 ≤ kernelInverseLog q n j d p := by unfold kernelInverseLog; positivity
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have he : 0 ≤ (q : ℝ) * (d + 1) := by positivity
  unfold kernelGeometryLog
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScalarEnvelope
namespace OAI

section

namespace Erdos3

theorem kernelGeometryLog_le_envelope {q n j k d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hk : (k : ℝ) ≤ D) (hd : (d : ℝ) ≤ D) :
    kernelGeometryLog q n j k d p ≤ kernelGeometryEnvelope D p := by
  have hi := kernelInverseLog_le_envelope hD hp hq hn hj hd
  unfold kernelGeometryLog kernelGeometryEnvelope
  gcongr

theorem kernelRowOutputLog_le_envelope {q n j k u d : ℕ} {D p : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : (q : ℝ) ≤ D) (hn : (n : ℝ) ≤ D)
    (hj : (j : ℝ) ≤ D) (hk : (k : ℝ) ≤ D) (hu : (u : ℝ) ≤ D)
    (hd : (d : ℝ) ≤ D) (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    kernelRowOutputLog q n j k u d p ≤ kernelOutputEnvelope D p := by
  have hG := kernelGeometryLog_le_envelope hD hp hq hn hj hk hd
  have hG0 := (kernelGeometryLog_bounds q n j k d hp).1
  have hGe := kernelGeometryEnvelope_nonneg hD hp
  dsimp only [kernelRowOutputLog, kernelOutputEnvelope, affineProfileLogBound, jetOutputRadiusLog]
  gcongr

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

theorem AllocatedComparisonDimensions.kernel_coefficients
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (Fintype.card (BoundedIntegerExponent G (j.val+1)) : ℝ) ≤ D := by
  have hc := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  rw [Fintype.card_sum] at hc
  exact (Nat.cast_le.mpr (by omega)).trans (h.coefficients j)

theorem AllocatedComparisonDimensions.nonkernel_coefficients
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) : ℝ) ≤ D := by
  have hc := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  rw [Fintype.card_sum] at hc
  exact (Nat.cast_le.mpr (by omega)).trans (h.coefficients j)

variable (h : AllocatedComparisonDimensions (G := G) B α O D) {p e : ℝ} (hp : 0 ≤ p)

include h hp

theorem allocatedDensityLog_le_envelope :
    allocatedDensityLog (G := G) B α O p ≤ allocatedDensityEnvelope m D p := by
  have hD := h.nonneg
  have ht : 0 ≤ 4*(p+8) := by positivity
  have hk (j : Fin m) := kernelRowOutputLog_le_envelope h.nonneg ht h.cube h.kernel_variables
    (h.rows j) (h.kernel_coefficients B j) (h.nonkernel_coefficients B j)
    (h.layer_degree B j) h.profile
  have hsum : (∑ j : Fin m, kernelRowOutputLog (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (Fintype.card (BoundedIntegerExponent G (j.val+1)))
      (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j)) (j.val+1) (4*(p+8))) ≤
      (m : ℝ)*kernelOutputEnvelope D (4*(p+8)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hk j)
  have hc (j : Fin m) : allocatedDensityColumnLog (G := G) B α j ≤ D+3*D*D+D*(D+1) := by
    have hd := h.layer_degree B j
    have hn := h.nonkernel_coefficients B j
    have hparam := h.parameters
    have hq := h.cube
    have hplus : (j.val : ℝ)+2 ≤ D+1 := by
      push_cast at hd
      linarith
    unfold allocatedDensityColumnLog
    push_cast at hd ⊢
    gcongr
  have hcols : (∑ j : Fin m, allocatedDensityColumnLog (G := G) B α j) ≤
      (m : ℝ)*(D+3*D*D+D*(D+1)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  unfold allocatedDensityLog allocatedDensityEnvelope kernelFamilyOutputLog
  linarith

theorem allocatedJetSupportLog_le_envelope :
    allocatedJetSupportLog (G := G) B α O p ≤ allocatedSupportEnvelope m D p := by
  have hD := h.nonneg
  have hden := allocatedDensityLog_le_envelope B h hp
  have hc (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) ≤ D+D*(D+1) := by
    have hd := h.layer_degree B j
    have hn := h.coefficients j
    have hq := h.cube
    gcongr
  have hs : (∑ j : Fin m,
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1))) ≤ (m : ℝ)*(D+D*(D+1)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  unfold allocatedJetSupportLog allocatedSupportEnvelope
  linarith

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem inverseProduct_norm_le_exp {Q : Type*} [Fintype Q]
    (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q) {p : ℝ}
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) :
    ‖(∏ q, R q)⁻¹‖ ≤ Real.exp ((Fintype.card Q : ℝ) * p) := by
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Finset.prod_nonneg (fun q _ => hR q))),
    ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ _q : Q, Real.exp p :=
      Finset.prod_le_prod (fun q _ => inv_nonneg.mpr (hR q)) (fun q _ => hRi q)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

theorem diagonalProfileLip_le_exp {Q : Type*} [Fintype Q]
    (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q) {D p e : ℝ} {δ : ℝ≥0}
    (hp : 0 ≤ p) (he : 0 ≤ e)
    (hcard : (Fintype.card Q : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D)
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e) :
    (‖(∏ q, R q)⁻¹‖₊ *
      (affineProductProfileLip Q δ * NNReal.mk (Real.exp p) (Real.exp_pos p).le) : ℝ≥0) ≤
      Real.exp (D * p + 2 * D + (D + 1) * e + p) := by
  have hJ : ‖(∏ q, R q)⁻¹‖ ≤ Real.exp (D * p) :=
    (inverseProduct_norm_le_exp R hR hRi).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hp))
  have hL : (affineProductProfileLip Q δ : ℝ) ≤ Real.exp (2 * D + (D + 1) * e) := by
    apply (affineProductProfileLip_le_exp Q hδ).trans
    apply Real.exp_le_exp.mpr
    unfold affineProfileLogBound
    nlinarith
  simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nnnorm]
  calc
    _ ≤ Real.exp (D * p) * (Real.exp (2 * D + (D + 1) * e) * Real.exp p) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedIdealRefinedPointwise
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)

include h

theorem AllocatedComparisonDimensions.active_outputs
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] :
    (Fintype.card (Σ a : {a // ¬P a}, O a.val.1) : ℝ) ≤ D := by
  let emb : (Σ a : {a // ¬P a}, O a.val.1) ↪ (Σ a : LayerSamplerAxis I n, O a.1) :=
    Function.Embedding.sigmaMap (Function.Embedding.subtype (fun a => ¬P a))
      (fun a => Function.Embedding.refl (O a.val.1))
  have hc := Fintype.card_le_of_embedding emb
  exact (Nat.cast_le.mpr hc).trans h.outputs

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedAffineL1_primitive_bounds_s2_oai {D P Prho Pk : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hP : 0 ≤ P) (hPrho : 0 ≤ Prho) (hPk : 0 ≤ Pk)
    {Mk : ℕ} (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (partition : LayerSamplerAxis I n → Prop)
    (R : Fin m → ℝ) (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho) :
    let L := allocatedAffineL1Log m D P Prho Pk
    let Output := Σ a : {a // ¬partition a}, O a.val.1
    0 ≤ L ∧ P ≤ L ∧
      allocatedDensityLog (G := G) B α O P ≤ L ∧
      allocatedJetSupportLog (G := G) B α O P ≤ L ∧
      (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) ≤ Real.exp L ∧
      partitionedIdealRadius α m + 1 ≤ Real.exp L ∧
      ‖(∏ o : Output, |R o.1.val.1|)⁻¹‖ *
        ((affineProductProfileLip Output ρ : ℝ) * Real.exp P) ≤ Real.exp L ∧
      ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk ≤ L ∧
      scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) ≤ Real.exp L := by
  intro L Output
  have hD := hdim.nonneg
  have hden := allocatedDensityEnvelope_nonneg m hD hP
  have hsupp := allocatedSupportEnvelope_nonneg m hD hP
  have hindex : 0 ≤ ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk := mul_nonneg (Nat.cast_nonneg _) hPk
  have hlip : 0 ≤ allocatedIdealLipEnvelope D P Prho := by
    unfold allocatedIdealLipEnvelope
    positivity
  have hradius : 0 ≤ ((m + 1 : ℕ) : ℝ) * D + 2 := by positivity
  have hboundary : 0 ≤ scalarCubeRiemannLog D := by unfold scalarCubeRiemannLog; positivity
  have hpieces : 0 ≤ L ∧ P ≤ L ∧
      ((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk + allocatedDensityEnvelope m D P ≤ L ∧
      allocatedSupportEnvelope m D P ≤ L ∧ allocatedIdealLipEnvelope D P Prho ≤ L ∧
      ((m + 1 : ℕ) : ℝ) * D + 2 ≤ L ∧ scalarCubeRiemannLog D ≤ L := by
    dsimp only [L, allocatedAffineL1Log]
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  have hdenL : allocatedDensityEnvelope m D P ≤ L := by linarith only [hpieces.2.2.1, hindex]
  refine ⟨hpieces.1, hpieces.2.1, (allocatedDensityLog_le_envelope B hdim hP).trans hdenL,
    (allocatedJetSupportLog_le_envelope B hdim hP).trans hpieces.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (((m * 2 ^ (m + 1) : ℕ) : ℝ) * Pk) * Real.exp (allocatedDensityEnvelope m D P) :=
        mul_le_mul (layerKernelIndexBound_le_exp m hMk)
          (Real.exp_le_exp.mpr (allocatedDensityLog_le_envelope B hdim hP)) (Real.exp_nonneg _) (Real.exp_nonneg _)
      _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hpieces.2.2.1
  · apply (partitionedIdealRadius_add_one_le_exp α m).trans
    apply Real.exp_le_exp.mpr
    have hdim' := mul_le_mul_of_nonneg_left hdim.cube (by positivity : 0 ≤ (m : ℝ) + 1)
    have hb := hpieces.2.2.2.2.2.1
    push_cast at hb
    linarith
  · have hk := diagonalProfileLip_le_exp (fun o : Output => R o.1.val.1)
      (fun o => hR o.1.val.1) hP hPrho (hdim.active_outputs B partition) hdim.profile
      (fun o => hRi o.1.val.1) hρ
    simp only [NNReal.coe_mul, NNReal.coe_mk, coe_nnnorm] at hk
    simp_rw [abs_of_nonneg (hR _)]
    exact hk.trans (Real.exp_le_exp.mpr hpieces.2.2.2.2.1)
  · linarith only [hpieces.2.2.1, hden]
  · exact (scalarCubeRiemannBoundary_le_exp α hD hdim.cube).trans
      (Real.exp_le_exp.mpr hpieces.2.2.2.2.2.2)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedAffineL1_primitive_bounds_s2_oai.{u_1, u_2, u_3, u_4, u_5}
