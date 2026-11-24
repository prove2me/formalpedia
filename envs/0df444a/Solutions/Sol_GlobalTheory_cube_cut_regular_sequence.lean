-- Prove2me | solution 1 for GlobalTheory.cube_cut_regular_sequence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:43.770852+00:00
-- url     : https://prove2.me/submissions/9913932c-3c1b-4549-b252-07f20f6d01c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CubeCutRegularSequence
import Theorems.Thm_GlobalTheory_CubeCut_exactMod_of_exact
import Theorems.Thm_GlobalTheory_CubeCut_ExactMod_mem_empty
import Theorems.Thm_GlobalTheory_CubeCut_ExactMod_exists_glue
import Theorems.Thm_GlobalTheory_CubeCut_ExactMod_cut
import Theorems.Thm_GlobalTheory_CubeCut_res_mem_imSum
import Theorems.Thm_GlobalTheory_CubeCut_imSum_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory GlobalTheory
open GlobalTheory
open CubeCut
namespace GlobalTheory
theorem _root_.solution : ∀ (K : Type) [CommRing K] (I : Type) [LinearOrder I] [Fintype I] (g : ℕ) (n : ℤ) (C : ℤ → Cube.{0} I K) (mu : Fin g → ∀ l l', C l ⟶ C l'), 0 < n → (∀ i j l l' l'', l' = l + n → l'' = l' + n → mu i l l' ≫ mu j l' l'' = mu j l l' ≫ mu i l' l'') → (∀ (T : Finset I), T.Nonempty → ∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj T), l' = l + n → ((mu i l l').app T).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app T).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app T).hom) → (∀ l, 0 < l → ∀ p, (cubeComplex (C l)).ExactAt p) → (∀ (i : Fin g) (l l' : ℤ) (y : (C l).obj ∅), l' = l + n → (i : ℕ) * n < l → ((mu i l l').app ∅).hom y ∈ (⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j l l').app ∅).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < i), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ l : ℤ, g * n < l → (∀ y : (C l).obj ∅, (∀ a : I, Cube.res (C l) (Finset.empty_subset {a}) y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom) → y ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app ∅).hom) ∧ ∀ y : ∀ a : I, (C l).obj {a}, (∀ a a' : I, Cube.res (C l) (show ({a} : Finset I) ⊆ {a, a'} by simp) (y a) - Cube.res (C l) (show ({a'} : Finset I) ⊆ {a, a'} by simp) (y a') ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a, a'}).hom) → ∃ y₀ : (C l).obj ∅, ∀ a, Cube.res (C l) (Finset.empty_subset {a}) y₀ - y a ∈ ⨆ (j : Fin g) (_ : (j : ℕ) < g), LinearMap.range ((mu j (l - n) l).app {a}).hom := by
  intro K _ I _ _ g n C mu hn hcomm hreg hac
  have P : ∀ k : ℕ, k ≤ g → ∀ l₀ l : ℤ, l = l₀ + n → (k : ℤ) * n < l →
      CubeCut.ExactMod (C l) (fun s => CubeCut.imSum (fun j => mu j l₀ l) k s) := by
    intro k
    induction k with
    | zero =>
      intro _ l₀ l _ hlt
      refine CubeCut.exactMod_of_exact (fun s => ?_) (hac l (by simpa using hlt))
      simp [CubeCut.imSum]
    | succ k ih =>
      intro hk l₀ l hl hlt
      push_cast at hlt
      have hA := ih (by omega) (l₀ - n) l₀ (by ring) (by linarith)
      have hB := ih (by omega) l₀ l hl (by linarith)
      let i : Fin g := ⟨k, by omega⟩
      refine CubeCut.ExactMod.cut (mu i l₀ l) hA hB
        (fun h x hx => CubeCut.res_mem_imSum _ _ h x hx) ?_
        (fun s hs x hx => hreg s hs i l₀ l x hl hx)
        (fun s => CubeCut.imSum_succ (fun j => mu j l₀ l) i s)
      intro s x hx
      have key : CubeCut.imSum (fun j => mu j (l₀ - n) l₀) k s ≤
          (CubeCut.imSum (fun j => mu j l₀ l) k s).comap ((mu i l₀ l).app s).hom := by
        refine iSup₂_le fun j hj => ?_
        rintro _ ⟨z, rfl⟩
        rw [Submodule.mem_comap]
        have e := congrArg (fun f => (f.app s).hom z) (hcomm j i (l₀ - n) l₀ l (by ring) hl)
        simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at e
        rw [e]
        exact Submodule.mem_iSup_of_mem j
          (Submodule.mem_iSup_of_mem hj (LinearMap.mem_range_self _ _))
      exact key hx
  refine ⟨fun i l l' y hl' hlt hy => ?_, fun l hlt => ?_⟩
  · have hE := P i i.2.le (l - n) l (by ring) hlt
    refine hE.mem_empty y fun a => ?_
    refine hreg {a} (Finset.singleton_nonempty a) i l l' _ hl' ?_
    rw [Cube.app_res]
    exact CubeCut.res_mem_imSum _ _ _ _ hy
  · have hE := P g le_rfl (l - n) l (by ring) hlt
    exact ⟨hE.mem_empty, hE.exists_glue⟩
end GlobalTheory
