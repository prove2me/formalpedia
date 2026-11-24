-- Prove2me | solution 1 for GlobalTheory.existsUnique_factor_completedStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:51.07527+00:00
-- url     : https://prove2.me/submissions/bbcd0f67-60d8-4e77-a455-117a1a410a27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_existsUnique_extend_adicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
omit [IsLocalRing R]
namespace GlobalTheory
theorem _root_.solution (I : Ideal R) [IsAdicComplete I R]
    {f : Spec (.of R) ⟶ X} {x : X}
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f)
    (hfg : (maximalIdeal (X.presheaf.stalk x)).FG)
    (hk : ∃ k : ℕ, (maximalIdeal (X.presheaf.stalk x)).map φ.hom ^ k ≤ I) :
    ∃! ψ : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R,
      Spec.map (CommRingCat.ofHom ψ) ≫ fromSpecCompletedStalk X x = f := by
  refine (existsUnique_congr fun ψ => ?_).mp
    (existsUnique_extend_adicCompletion (R := R) φ.hom hfg I hk)
  rw [fromSpecCompletedStalk, ← Spec.map_comp_assoc, ← hφ, cancel_mono, ← CommRingCat.ofHom_comp]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact congr($(Spec.map_injective h).hom)
end GlobalTheory
