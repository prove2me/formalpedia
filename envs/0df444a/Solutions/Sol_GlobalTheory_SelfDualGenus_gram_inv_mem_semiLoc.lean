-- Prove2me | solution 1 for GlobalTheory.SelfDualGenus.gram_inv_mem_semiLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:57:18.892584+00:00
-- url     : https://prove2.me/submissions/8c83ed5c-9b17-470b-964b-038d24a99e0f

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_TraceFormDualOneTraceFormDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_cc_mem_semiLoc
import Theorems.Thm_GlobalTheory_SelfDualGenus_herm_eq_dotProduct
import Theorems.Thm_GlobalTheory_SelfDualGenus_herm_mulVec
import Theorems.Thm_GlobalTheory_SelfDualGenus_one_notMem
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_Published_cc_ne_zero
import Theorems.Thm_GlobalTheory_Published_det_map_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing
open scoped Matrix TensorProduct nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalLattice
noncomputable section
open GlobalTheory GlobalTheory.SelfDualGenus
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))
variable {G : Matrix (Fin r) (Fin r) E} {L : Submodule (𝓞 E) (Fin r → E)}
  {𝔟 : FractionalIdeal (𝓞 E)⁰ E} {g : GL (Fin r) E} {b : E}
namespace GlobalTheory.SelfDualGenus
theorem _root_.solution (hd : G.det ≠ 0) (hL : L.FG)
    (hmod : ∀ x, x ∈ L ↔ ∀ y ∈ L, herm G x y ∈ 𝔟)
    (hg : ∀ x, (∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L) ↔
      ∀ i, (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x) i ∈ semiLoc v) (hb0 : b ≠ 0)
    (hb : ∀ z, (∃ s ∉ v.asIdeal, (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * z ∈ 𝔟) ↔ b⁻¹ * z ∈ semiLoc v)
    (i j : Fin r) :
    b * ((g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc)⁻¹ i j ∈
      semiLoc v := by
  set H := (g : Matrix (Fin r) (Fin r) E)ᵀ * G * (g : Matrix (Fin r) (Fin r) E).map cc with hH
  have hHd : IsUnit H.det := by
    have := g.det_ne_zero
    rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Published.det_map_cc]
    exact (mul_ne_zero (mul_ne_zero this hd) (Published.cc_ne_zero this)).isUnit
  let a : Fin r → E := b • (Pi.single i 1 ᵥ* H⁻¹)
  let x : Fin r → E := (g : Matrix (Fin r) (Fin r) E) *ᵥ a
  have hx : ∀ y, herm G x y =
      b * cc ((((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) i) := by
    intro y
    have hy : y = (g : Matrix (Fin r) (Fin r) E) *ᵥ
        (((g⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [hy, herm_mulVec, ← hH, HermitianTraceFormVanishing.herm_smul_left, herm_eq_dotProduct,
      Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hHd, Matrix.vecMul_one,
      single_dotProduct, one_mul]
  have hloc : ∀ y ∈ L, ∃ s ∈ v.asIdeal.primeCompl,
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * herm G x y ∈ 𝔟 := fun y hy => by
    refine (hb _).2 ?_
    rw [hx, inv_mul_cancel_left₀ hb0]
    exact cc_mem_semiLoc v ((hg y).1 ⟨1, one_notMem v, by simpa using hy⟩ i)
  have hmul : ∀ (c : 𝓞 E) {z : E}, z ∈ 𝔟 → (c : E) * z ∈ 𝔟 := fun c z hz =>
    (𝔟 : Submodule (𝓞 E) E).smul_mem c hz
  obtain ⟨t, ht⟩ := hL
  obtain ⟨s, hs, h⟩ := exists_mem_submonoid_forall t.finite_toSet v.asIdeal.primeCompl
    (fun y s => (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) * herm G x y ∈ 𝔟)
    (fun y s s' h => by
      have := hmul (algebraMap _ (𝓞 E) s') h
      simpa [mul_assoc] using this)
    (fun y hy => hloc y (ht ▸ Submodule.subset_span hy))
  have hsx : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x ∈ L := by
    refine (hmod _).2 fun y hy => ?_
    rw [← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_left]
    rw [← ht] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simpa [herm, cc] using 𝔟.zero_mem
    | add y z _ _ hy hz =>
      rw [herm_add_right, mul_add]
      exact (𝔟 : Submodule (𝓞 E) E).add_mem hy hz
    | smul c y _ hy =>
      rw [← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_right, mul_left_comm]
      exact hmul (IsCMField.ringOfIntegersComplexConj E c) hy
  have := (hg x).1 ⟨s, hs, hsx⟩ j
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
  simpa [a] using this
end GlobalTheory.SelfDualGenus
