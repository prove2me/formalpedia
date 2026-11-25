-- Prove2me | solution 1 for GlobalTheory.UnitLemma.latProj_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:45.038577+00:00
-- url     : https://prove2.me/submissions/8ff638ee-87a0-46b1-9bf4-14ff2dea418d

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_StableLatticePairProjectionSmulUnits
import Theorems.Thm_GlobalTheory_UnitLemma_latPair_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
theorem _root_.solution (O E A₁ A₂ : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂] (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (M : stLat O E ((g₁, g₂) : A₁ × A₂)) :
    latProj O E g₁ g₂ (t • M) = t • latProj O E g₁ g₂ M := by
  rw [latPair_smul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).comap (LinearMap.inl O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.fst A₁ A₂) t : A₁ˣ) : A₁) ((M : Submodule O (A₁ × A₂)).comap (LinearMap.inl O A₁ A₂))
    ext y
    rw [Submodule.mem_comap, mem_mulLat_iff, mem_mulLat_iff, Submodule.mem_comap]
    have h : ((t⁻¹ : (A₁ × A₂)ˣ) : A₁ × A₂) * (LinearMap.inl O A₁ A₂ y) =
        LinearMap.inl O A₁ A₂ (((Units.map (MonoidHom.fst A₁ A₂) t)⁻¹ : A₁ˣ) * y) := by
      ext <;> simp
    rw [h]
  · change (mulLat O (t : A₁ × A₂) (M : Submodule O (A₁ × A₂))).map (LinearMap.snd O A₁ A₂) =
      mulLat O ((Units.map (MonoidHom.snd A₁ A₂) t : A₂ˣ) : A₂) ((M : Submodule O (A₁ × A₂)).map (LinearMap.snd O A₁ A₂))
    unfold mulLat
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
end GlobalTheory.UnitLemma
