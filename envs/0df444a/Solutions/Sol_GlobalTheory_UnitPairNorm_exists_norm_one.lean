-- Prove2me | solution 1 for GlobalTheory.UnitPairNorm.exists_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:11.061723+00:00
-- url     : https://prove2.me/submissions/417b63c1-f706-4cc1-a6fb-41e84dc8eab7

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnitNorm
import Theorems.Thm_GlobalTheory_UnitPairNorm_h_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitPairNorm
open Module
variable {O E : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E]
  [Algebra O E] [IsFractionRing O E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
namespace GlobalTheory.UnitPairNorm
theorem _root_.solution (c : E ≃+* E)
    (hnorm : ∀ u : Oˣ, c (algebraMap O E u) = algebraMap O E u →
      ∃ z : Oˣ, algebraMap O E u = algebraMap O E z * c (algebraMap O E z))
    (h : V → V → E)
    (hsmul : ∀ (s : E) (x z : V), h (s • x) z = s * h x z)
    (hsym : ∀ x y : V, h y x = c (h x y))
    (L : Submodule O V) (e : V) (he : e ∈ L) (u : Oˣ) (hu : h e e = algebraMap O E u) :
    ∃ e' ∈ L, h e' e' = 1 := by
  have hfix : c (algebraMap O E u) = algebraMap O E u := by
    rw [← hu]; exact (hsym e e).symm
  obtain ⟨w, hw⟩ := hnorm u hfix
  refine ⟨((w⁻¹ : Oˣ) : O) • e, L.smul_mem _ he, ?_⟩
  rw [← algebraMap_smul E, hsmul, h_smul_right c h hsmul hsym, hu, hw]
  have h1 : algebraMap O E ((w⁻¹ : Oˣ) : O) * algebraMap O E (w : O) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : c (algebraMap O E ((w⁻¹ : Oˣ) : O)) * c (algebraMap O E (w : O)) = 1 := by
    rw [← map_mul, h1, map_one]
  linear_combination (c (algebraMap O E ((w⁻¹ : Oˣ) : O)) * c (algebraMap O E (w : O))) * h1 + h2
end GlobalTheory.UnitPairNorm
