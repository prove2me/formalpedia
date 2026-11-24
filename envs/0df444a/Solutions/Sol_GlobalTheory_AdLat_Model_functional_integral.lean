-- Prove2me | solution 1 for GlobalTheory.AdLat.Model.functional_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:08:21.749608+00:00
-- url     : https://prove2.me/submissions/ca8ac323-eb53-4edd-9fca-f8ca75387373

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Theorems.Thm_GlobalTheory_AdLat_Model_integral_iff
import Theorems.Thm_GlobalTheory_AdLat_Model_ext_tmul

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
theorem _root_.solution {n : ℕ} (L : Set (Fin n → E)) (φ : (Fin n → E) →ₗ[F] F)
    (hφ : ∀ x ∈ L, φ x ∈ (algebraMap (𝓞 F) F).range) {w : Fin n → E} (hw : fv F w ∈ hat F L) :
    φ w ∈ (algebraMap (𝓞 F) F).range := by
  have key : ∀ z ∈ hat F L, ∀ v, ext φ z v ∈ v.adicCompletionIntegers F := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      intro v
      rw [ext_tmul]
      exact mul_mem ((integral_iff _).2 (hφ x hx) v) (ha v)
    | zero => intro v; rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => intro v; rw [map_add]; exact add_mem (hx v) (hy v)
    | neg x _ hx => intro v; rw [map_neg]; exact neg_mem (hx v)
  have h := key _ hw
  unfold fv at h
  rw [ext_tmul, mul_one] at h
  exact (integral_iff _).1 h
end GlobalTheory.AdLat.Model
