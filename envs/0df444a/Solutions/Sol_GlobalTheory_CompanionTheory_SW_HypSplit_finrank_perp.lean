-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HypSplit.finrank_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:22.390869+00:00
-- url     : https://prove2.me/submissions/39cf42bb-786c-48f4-a2a4-75cfa22dd7c3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hLin_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hE_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.SW.HypSplit.hLin_apply

set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HypSplit
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}
namespace GlobalTheory.CompanionTheory.SW.HypSplit
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j)
    {x y : Fin M → E} (hxx : hE σ J x x = 0) (hyy : hE σ J y y = 0) (hxy : hE σ J x y = 1) :
    Module.finrank E (LinearMap.ker ((hLin σ J x).prod (hLin σ J y))) + 2 = M := by
  have hyx : hE σ J y x = 1 := by rw [← hE_conj hσ hJ, hxy, map_one]
  have hs : Function.Surjective ((hLin σ J x).prod (hLin σ J y)) := by
    rintro ⟨a, b⟩
    refine ⟨a • y + b • x, Prod.ext ?_ ?_⟩
    · change hLin σ J x (a • y + b • x) = a
      simp only [map_add, map_smul, hLin_apply, smul_eq_mul, hxy, hxx, mul_one, mul_zero, add_zero]
    · change hLin σ J y (a • y + b • x) = b
      simp only [map_add, map_smul, hLin_apply, smul_eq_mul, hyy, hyx, mul_one, mul_zero, zero_add]
  have h := LinearMap.finrank_range_add_finrank_ker ((hLin σ J x).prod (hLin σ J y))
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_prod, Module.finrank_self,
    Module.finrank_fin_fun] at h
  omega
end GlobalTheory.CompanionTheory.SW.HypSplit
