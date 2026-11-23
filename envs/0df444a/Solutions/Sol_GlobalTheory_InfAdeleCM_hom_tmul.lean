-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.hom_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:35.064852+00:00
-- url     : https://prove2.me/submissions/adccd00c-f952-450d-a25d-684073811edb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Theorems.Thm_GlobalTheory_InfAdeleCM_continuous_ext
import Theorems.Thm_GlobalTheory_InfAdeleCM_ext_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
open GlobalTheory GlobalTheory.InfAdeleCM
variable {F : Type} [Field F] [NumberField F]
variable {E : Type} [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.InfAdeleCM
theorem _root_.solution [IsTotallyReal F] (τ : E →+* ℂ) (θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ)
    (h1 : ∀ x, θ (1 ⊗ₜ x) = τ x) (h2 : Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)))
    (a : InfiniteAdeleRing F) (x : E) :
    θ (a ⊗ₜ x) = ext (τ.comp (algebraMap F E)) a * τ x := by
  have : (fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E))) = ext (τ.comp (algebraMap F E)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer h2 (continuous_ext _) ?_
    funext y
    simp only [Function.comp_apply, ext_algebraMap, RingHom.comp_apply]
    rw [← h1, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [← this, ← h1, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
end GlobalTheory.InfAdeleCM
