-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.exists_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:28.020803+00:00
-- url     : https://prove2.me/submissions/583707bd-7df4-4e66-bd6c-464cb794213a

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pairMap_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pair_form
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_pairMap_injective
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_extend_isom

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
    (hd : δ ≠ 0) {l' : ℕ} (hl : l ≤ l') {e f : Fin l → V} {W : Submodule L V}
    {e' f' : Fin l' → V} {W' : Submodule L V}
    (F : IsFrame h δ e f W) (F' : IsFrame h δ e' f' W') :
    ∃ g : V ≃ₗ[L] V, IsIso h g ∧ (∀ i, g (e i) = e' (Fin.castLE hl i)) ∧
      ∀ i, g (f i) = f' (Fin.castLE hl i) := by
  obtain ⟨he, hf, hef, -, -, -⟩ := F
  obtain ⟨he', hf', hef', -, -, -⟩ := F'
  have hι : Function.Injective (Fin.castLE hl) := Fin.castLE_injective hl
  have he2 : ∀ i j, h (e' (Fin.castLE hl i)) (e' (Fin.castLE hl j)) = 0 := fun i j => he' _ _
  have hf2 : ∀ i j, h (f' (Fin.castLE hl i)) (f' (Fin.castLE hl j)) = 0 := fun i j => hf' _ _
  have hef2 : ∀ i j, h (e' (Fin.castLE hl i)) (f' (Fin.castLE hl j)) = if i = j then δ else 0 := by
    intro i j
    rw [hef']
    simp only [hι.eq_iff]
  have Tinj := pairMap_injective hh hd he hf hef
  have T'inj := pairMap_injective (e := fun i => e' (Fin.castLE hl i))
    (f := fun i => f' (Fin.castLE hl i)) hh hd he2 hf2 hef2
  let T : ((Fin l → L) × (Fin l → L)) →ₗ[L] V := pairMap e f
  let T' : ((Fin l → L) × (Fin l → L)) →ₗ[L] V :=
    pairMap (fun i => e' (Fin.castLE hl i)) (fun i => f' (Fin.castLE hl i))
  let E := LinearEquiv.ofInjective T Tinj
  have hφE : ∀ p, (T' ∘ₗ E.symm.toLinearMap) (E p) = T' p := fun p => by simp
  have hEv : ∀ p, ((E p : LinearMap.range T) : V) = T p := fun p => rfl
  obtain ⟨g, hg, hgφ⟩ := extend_isom hs hh (LinearMap.range T) (T' ∘ₗ E.symm.toLinearMap)
    (T'inj.comp E.symm.injective) (by
      intro x y
      obtain ⟨p, rfl⟩ := E.surjective x
      obtain ⟨r, rfl⟩ := E.surjective y
      rw [hφE, hφE, hEv, hEv]
      exact (pair_form hh he2 hf2 hef2 p r).trans (pair_form hh he hf hef p r).symm)
  have hgT : ∀ p, g (T p) = T' p := fun p => by
    have := hgφ (E p)
    rwa [hφE, hEv] at this
  refine ⟨g, hg, fun i => ?_, fun i => ?_⟩
  · have := hgT (Pi.single i 1, 0)
    simpa [T, T', pairMap_apply, Pi.single_apply] using this
  · have := hgT (0, Pi.single i 1)
    simpa [T, T', pairMap_apply, Pi.single_apply] using this
end GlobalTheory.CompanionTheory.FlWitt
