-- Prove2me | solution 1 for GlobalTheory.exists_units_hom_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:22:23.069002+00:00
-- url     : https://prove2.me/submissions/9c181431-d721-47f4-a6fd-a6c328705052

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AlgebraMapPadicIntFinExtInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Γ R S : Type} [Group Γ] [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (c : Γ →* Sˣ) (hex : ∀ g, ∃ y : R, φ y = (c g : S)) :
    ∃ χ : Γ →* Rˣ, ∀ g, φ (χ g : R) = (c g : S) := by
  choose y hy using hex
  have hinv : ∀ g, y g * y g⁻¹ = 1 := fun g => hφ (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hinv' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hinv g⁻¹
  let u : Γ → Rˣ := fun g => ⟨y g, y g⁻¹, hinv g, hinv' g⟩
  refine ⟨{ toFun := u, map_one' := ?_, map_mul' := ?_ }, fun g => hy g⟩
  · ext
    apply hφ
    simp [u, hy]
  · intro g h
    ext
    apply hφ
    simp [u, hy]
end GlobalTheory
