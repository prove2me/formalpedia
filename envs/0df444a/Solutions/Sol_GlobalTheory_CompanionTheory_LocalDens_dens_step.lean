-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.dens_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:09.516185+00:00
-- url     : https://prove2.me/submissions/08190d8f-3185-4d9c-950f-97342fcdbd17

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_solCount_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_card_fibers
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_card_preimage_hom
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_piM_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_piH_surj
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gb_red
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_mem_sol
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalDens_gr_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hfin : ∀ k, Finite (R ⧸ lev ϖ k)) (hinv : ∀ a, σ (σ a) = a)
    (hσ : σ ϖ = ϖ) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (k : ℕ)
    (hS : cT σ S = S) (hT : cT σ T = T)
    (hfib : ∀ h : Matrix (Fin n) (Fin n) R, cT σ h = h → red ϖ k h = red ϖ k T →
      solCount σ ϖ S h (k + 1) = solCount σ ϖ S T (k + 1)) :
    densAt σ ϖ S T k = densAt σ ϖ S T (k + 1) := by
  haveI := hfin
  haveI : ∀ k a b, Finite (Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k)) := fun k a b =>
    inferInstanceAs (Finite (Fin a → Fin b → R ⧸ lev ϖ k))
  have hTm : red ϖ k T ∈ hermSub σ ϖ n k := ⟨T, hT, rfl⟩
  have h1 := card_preimage_hom (piM ϖ k m n) (piM_surj ϖ k m n) (sol σ ϖ S T k)
  have h2 := card_preimage_hom (piH σ ϖ n k) (piH_surj σ ϖ n k) {⟨red ϖ k T, hTm⟩}
  have hmem : ∀ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)), gb σ ϖ S (k + 1) y ∈ hermSub σ ϖ n (k + 1) := by
    intro y
    obtain ⟨x, rfl⟩ := red_surj ϖ (k + 1) y
    rw [gb_red hσ]
    exact ⟨_, gr_herm hinv hS x, rfl⟩
  have hpi : ∀ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)),
      gb σ ϖ S k (piM ϖ k m n y) = piM ϖ k n n (gb σ ϖ S (k + 1) y) := by
    intro y
    obtain ⟨x, rfl⟩ := red_surj ϖ (k + 1) y
    rw [gb_red hσ, piM_red, gb_red hσ, piM_red]
  have h3 : Nat.card ((piM ϖ k m n) ⁻¹' (sol σ ϖ S T k))
      = Nat.card ((piH σ ϖ n k) ⁻¹' {⟨red ϖ k T, hTm⟩}) * solCount σ ϖ S T (k + 1) := by
    have hD : ∀ y : (piM ϖ k m n) ⁻¹' (sol σ ϖ S T k), (⟨gb σ ϖ S (k + 1) y.1, hmem y.1⟩ : hermSub σ ϖ n (k + 1)) ∈
        (piH σ ϖ n k) ⁻¹' {⟨red ϖ k T, hTm⟩} := by
      intro y
      have := (mem_sol hσ S T k _).1 y.2
      rw [hpi] at this
      exact Subtype.ext this
    refine card_fibers (fun y => ⟨⟨gb σ ϖ S (k + 1) y.1, hmem y.1⟩, hD y⟩) _ (fun d => ?_)
    obtain ⟨⟨_, h, hh, rfl⟩, hd⟩ := d
    have hk : red ϖ k h = red ϖ k T := by
      have := congrArg Subtype.val (Set.mem_singleton_iff.1 hd)
      simpa [piH, piM_red] using this
    rw [← hfib h hh hk, solCount_eq]
    refine Nat.card_congr
      { toFun := fun y => ⟨y.1.1, (mem_sol hσ S h (k + 1) _).2 (by
          have := congrArg (fun w => w.1.1) y.2
          simpa using this)⟩
        invFun := fun z => ⟨⟨z.1, by
          show piM ϖ k m n z.1 ∈ sol σ ϖ S T k
          rw [mem_sol hσ, hpi, (mem_sol hσ S h (k + 1) _).1 z.2, piM_red, hk]⟩,
          Subtype.ext (Subtype.ext ((mem_sol hσ S h (k + 1) _).1 z.2))⟩
        left_inv := fun y => by simp
        right_inv := fun z => by simp }
  have hH : ∀ k, Nat.card (hermMod σ ϖ n k) = Nat.card (hermSub σ ϖ n k) := fun _ => rfl
  have hM : ∀ k, 0 < Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) := fun k => Nat.card_pos
  have hone : Nat.card ({⟨red ϖ k T, hTm⟩} : Set (hermSub σ ϖ n k)) = 1 := by simp
  rw [hone, one_mul] at h2
  rw [h3] at h1
  unfold densAt
  rw [hH, hH, div_eq_div_iff (by exact_mod_cast (hM k).ne') (by exact_mod_cast (hM (k + 1)).ne')]
  have key : solCount σ ϖ S T k * Nat.card (hermSub σ ϖ n k) * Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)))
      = solCount σ ϖ S T (k + 1) * Nat.card (hermSub σ ϖ n (k + 1)) * Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) := by
    rw [← h2]
    rw [solCount_eq σ ϖ S T k]
    calc _ = (Nat.card (sol σ ϖ S T k) * Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1)))) * Nat.card (hermSub σ ϖ n k) := by ring
      _ = _ := by rw [← h1]; ring
  exact_mod_cast key
end GlobalTheory.CompanionTheory.LocalDens
