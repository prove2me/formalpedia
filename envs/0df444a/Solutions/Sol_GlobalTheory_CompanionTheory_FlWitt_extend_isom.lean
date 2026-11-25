-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.extend_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:48:32.252042+00:00
-- url     : https://prove2.me/submissions/e94c2101-9df5-4b3d-be0e-37d92f5241b9

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_witt_extension_theorem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FlWitt
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ}
namespace GlobalTheory.CompanionTheory.FlWitt
theorem _root_.solution [CharZero L] [FiniteDimensional L V] (hs : ∀ x, s (s x) = x) (hh : IsHerm s h)
    (U : Submodule L V) (φ : U →ₗ[L] V) (hinj : Function.Injective φ)
    (hiso : ∀ x y : U, h (φ x) (φ y) = h x y) :
    ∃ g : V ≃ₗ[L] V, IsIso h g ∧ ∀ x : U, g x = φ x := by
  letI : StarRing L :=
    { star := s
      star_involutive := hs
      star_mul := fun a b => by rw [map_mul, mul_comm]
      star_add := map_add s }
  have hadd : ∀ x y z, h (x + y) z = h x z + h y z := fun x y z => by
    rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1, ← hh.2.2.1]
  have hsm : ∀ (c : L) x z, h (c • x) z = s c * h x z := fun c x z => by
    rw [hh.2.2.1 z (c • x), hh.2.1, map_mul, ← hh.2.2.1]
  let B : V →ₗ⋆[L] V →ₗ[L] L := LinearMap.mk₂'ₛₗ (starRingEnd L) (RingHom.id L) h hadd
    (fun c x z => hsm c x z) hh.1 (fun c x z => hh.2.1 c x z)
  have hB : ∀ x y, B x y = h x y := fun _ _ => rfl
  obtain ⟨g, hg, hgφ⟩ := witt_extension_theorem L V B
    (fun x y => (hh.2.2.1 x y).symm) (fun x hx => hh.2.2.2 x hx) U φ hinj hiso
  exact ⟨g, hg, hgφ⟩
end GlobalTheory.CompanionTheory.FlWitt
