-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FlWitt.frame_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:23.930692+00:00
-- url     : https://prove2.me/submissions/cc969e9d-9f18-4b19-beed-34f251c1fa66

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_h_zero_left
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_mem_of_perp
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_exists_isom

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
    ∃ (q : Fin l ≃ Fin l') (g : V ≃ₗ[L] V), IsIso h g ∧ (∀ i, g (e i) = e' (q i)) ∧
      (∀ i, g (f i) = f' (q i)) ∧ ∀ w, w ∈ W ↔ g w ∈ W' := by
  obtain ⟨g, hg, ge, gf⟩ := exists_isom hs hh hd hl F F'
  have hmove : ∀ y x, h y (g.symm x) = h (g y) x := fun y x => by
    have := hg y (g.symm x)
    simpa using this.symm
  have heq : l = l' := by
    by_contra hne
    have hlt : l < l' := lt_of_le_of_ne hl hne
    let j : Fin l' := ⟨l, hlt⟩
    have hj : ∀ i : Fin l, j ≠ Fin.castLE hl i := fun i hji => by
      have := congrArg Fin.val hji
      simp [j] at this
      omega
    have hx : g.symm (e' j) ∈ W := by
      refine mem_of_perp hh hd F _ (fun i => ?_) (fun i => ?_)
      · rw [hmove, ge]
        exact F'.1 _ _
      · rw [hmove, gf, hh.2.2.1 (e' j), F'.2.2.1, if_neg (hj i), map_zero]
    have h0 : g.symm (e' j) = 0 := by
      refine F.2.2.2.2.1 _ hx ?_
      rw [hmove]
      simpa using F'.1 j j
    have he0 : e' j = 0 := by simpa using h0
    have := F'.2.2.1 j j
    rw [he0, h_zero_left hh, if_pos rfl] at this
    exact hd this.symm
  subst heq
  refine ⟨Equiv.refl _, g, hg, fun i => ge i, fun i => gf i, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · refine mem_of_perp hh hd F' _ (fun i => ?_) (fun i => ?_)
    · have := ge i
      have hi : e' i = g (e i) := this.symm
      rw [hi, hg]
      exact (F.2.2.2.1 w hw i).1
    · have := gf i
      have hi : f' i = g (f i) := this.symm
      rw [hi, hg]
      exact (F.2.2.2.1 w hw i).2
  · refine mem_of_perp hh hd F _ (fun i => ?_) (fun i => ?_)
    · rw [← hg, show g (e i) = e' i from ge i]
      exact (F'.2.2.2.1 _ hw i).1
    · rw [← hg, show g (f i) = f' i from gf i]
      exact (F'.2.2.2.1 _ hw i).2
end GlobalTheory.CompanionTheory.FlWitt
