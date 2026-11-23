-- Prove2me | solution 1 for GlobalTheory.InfAdeleCM.exists_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:37.552849+00:00
-- url     : https://prove2.me/submissions/9340d865-671c-4cff-851f-a1e8ac2ff027

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
theorem _root_.solution [IsTotallyReal F] (τ : E →+* ℂ) :
    ∃ θ : InfiniteAdeleRing F ⊗[F] E →+* ℂ, (∀ x, θ (1 ⊗ₜ x) = τ x) ∧
      Continuous fun a : InfiniteAdeleRing F => θ (a ⊗ₜ (1 : E)) := by
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let f : InfiniteAdeleRing F →ₐ[F] ℂ :=
    { ext (τ.comp (algebraMap F E)) with commutes' := fun x => ext_algebraMap _ x }
  let g : E →ₐ[F] ℂ := { τ with commutes' := fun x => rfl }
  refine ⟨(Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom, ?_, ?_⟩
  · intro x
    simp [g]
  · have : (fun a : InfiniteAdeleRing F =>
        (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom (a ⊗ₜ (1 : E))) =
        ext (τ.comp (algebraMap F E)) := by
      funext a
      simp [f]
    rw [this]
    exact continuous_ext _
end GlobalTheory.InfAdeleCM
