-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.ext_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:12.132896+00:00
-- url     : https://prove2.me/submissions/cf9b435c-562a-4970-9e94-b103e60ff381

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Model
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.AdLat.Model
theorem _root_.solution {n : ℕ} (φ : (Fin n → E) →ₗ[F] F) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    ext φ (fun i => a ⊗ₜ x i) = algebraMap F _ (φ x) * a := by
  have hx : φ x = ∑ i, φ (Pi.single i (x i)) := by
    rw [← map_sum, Finset.univ_sum_single]
  rw [hx, ← Algebra.smul_def, Finset.sum_smul]
  simp [ext]
end GlobalTheory.AdLat.Model
