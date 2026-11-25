-- Prove2me | solution 1 for GroundTheory.GroupCoh.exists_lift_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:37:52.133688+00:00
-- url     : https://prove2.me/submissions/7433bb36-f738-44ab-82a2-21593ad44daf

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupProduct
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Theorems.Thm_GroundTheory_GroupCoh_comp_d_apply
import Theorems.Thm_GroundTheory_GroupCoh_exists_f_eq_of_g_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct groupCohomology Limits
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
include hX
namespace GroundTheory.GroupCoh
theorem _root_.solution {p : ℕ} (z : cocycles X.X₃ p) :
    ∃ (y : (Fin p → G) → X.X₂) (x : cocycles X.X₁ (p + 1)),
      (∀ v, X.g.hom (y v) = iCocycles X.X₃ p z v) ∧
        ∀ v, X.f.hom (iCocycles X.X₁ (p + 1) x v) =
          (inhomogeneousCochains.d X.X₂ p).hom y v := by
  have hg : Function.Surjective X.g.hom := (Rep.epi_iff_surjective X.g).1 hX.epi_g
  have hf : Function.Injective X.f.hom := (Rep.mono_iff_injective X.f).1 hX.mono_f
  choose y hy using fun v => hg (iCocycles X.X₃ p z v)
  have hdy : ∀ v, X.g.hom ((inhomogeneousCochains.d X.X₂ p).hom y v) = 0 := fun v => by
    rw [comp_d_apply, show (fun u => X.g.hom (y u)) = iCocycles X.X₃ p z from funext hy,
      d_iCocycles]
    rfl
  choose x hx using fun v => exists_f_eq_of_g_eq_zero hX _ (hdy v)
  have hdx : (inhomogeneousCochains.d X.X₁ (p + 1)).hom x = 0 := by
    funext v
    apply hf
    rw [comp_d_apply, show (fun u => X.f.hom (x u)) = (inhomogeneousCochains.d X.X₂ p).hom y
      from funext hx, Pi.zero_apply, map_zero]
    exact congr(($(inhomogeneousCochains.d_comp_d (n := p) (A := X.X₂))).hom y v)
  exact ⟨y, cocyclesMk x hdx, hy, fun v => by rw [iCocycles_mk]; exact hx v⟩
end GroundTheory.GroupCoh
