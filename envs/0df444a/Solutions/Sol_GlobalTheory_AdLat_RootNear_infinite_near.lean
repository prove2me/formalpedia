-- Prove2me | solution 1 for GlobalTheory.AdLat.RootNear.infinite_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:25.88087+00:00
-- url     : https://prove2.me/submissions/a3bdc62a-0b09-47d8-911e-572fecc7bd5c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIntegralUnitRootNormOneAdeleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAdeleRingTensorEquivInfiniteProdFiniteStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsRootNear
import Theorems.Thm_GlobalTheory_AdLat_RootNear_inv_near
import Theorems.Thm_GlobalTheory_AdLat_RootNear_half_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat.RootNear
theorem _root_.solution (c : E ≃ₐ[F] E) :
    letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
      moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
    ∀ V ∈ 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E), ∀ᶠ u in 𝓝 (1 : InfiniteAdeleRing F ⊗[F] E),
      u * sg (InfiniteAdeleRing F) c u = 1 →
      ∃ x ∈ V, ∃ y ∈ V, x * y = 1 ∧ x = u * sg (InfiniteAdeleRing F) c x := by
  classical
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) :=
    IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  intro V hV
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hev : ∀ v : InfinitePlace F, Continuous (fun a : InfiniteAdeleRing F => a v) :=
    fun v => continuous_apply v
  have hinv := inv_near (Algebra.TensorProduct.basis (InfiniteAdeleRing F) (Module.finBasis F E))
    (fun a v => (a v)⁻¹)
    (continuousAt_pi.2 fun v => ((hev v).continuousAt (x := 1)).inv₀ (one_ne_zero))
    (funext fun v => inv_one)
    (by
      have : ∀ v : InfinitePlace F, ∀ᶠ a in 𝓝 (1 : InfiniteAdeleRing F), a v ≠ 0 :=
        fun v => ((hev v).continuousAt (x := 1)).eventually_ne one_ne_zero
      filter_upwards [Filter.eventually_all.2 this] with a ha
      exact funext fun v => mul_inv_cancel₀ (ha v)) V hV
  let h : InfiniteAdeleRing F := algebraMap F _ 2⁻¹
  have hh : ∀ w : InfiniteAdeleRing F ⊗[F] E, 2 * (h • w) = w := by
    intro w
    rw [algebraMap_smul, ← map_ofNat (algebraMap F (InfiniteAdeleRing F ⊗[F] E)) 2, ← Algebra.smul_def,
      smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]
  have hcont : Continuous (fun u : InfiniteAdeleRing F ⊗[F] E => h • (1 + u)) :=
    (continuous_const.add continuous_id).const_smul h
  have ht := hcont.tendsto 1
  have h11 : h • ((1 : InfiniteAdeleRing F ⊗[F] E) + 1) = 1 := by
    rw [smul_add, ← two_mul, hh]
  rw [h11] at ht
  filter_upwards [ht hV, ht hinv] with u h1 h3 hu
  obtain ⟨y, hy, hxy⟩ := h3
  exact ⟨_, h1, y, hy, hxy, half_root F E c u _ hu (hh _)⟩
end GlobalTheory.AdLat.RootNear
