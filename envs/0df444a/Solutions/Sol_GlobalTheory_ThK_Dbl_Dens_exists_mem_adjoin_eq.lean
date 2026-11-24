-- Prove2me | solution 1 for GlobalTheory.ThK.Dbl.Dens.exists_mem_adjoin_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:57:08.463898+00:00
-- url     : https://prove2.me/submissions/542e714b-933a-45f0-8de5-6e84df83a10c

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_PairsD
import Theorems.Thm_GlobalTheory_ThK_Dbl_Dens_exists_smul_of_rank_le_aleph0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Dens
open Polynomial Cardinal
namespace GlobalTheory.ThK.Dbl.Dens
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
    (O : Set (Module.End ℂ V)) (hV : Module.rank ℂ V ≤ ℵ₀)
    (hirr : ∀ N : Submodule ℂ V, (∀ T ∈ O, ∀ x ∈ N, T x ∈ N) → N = ⊥ ∨ N = ⊤)
    (f : V →ₗ[ℂ] V) (s : Finset V) :
    ∃ T ∈ Algebra.adjoin ℂ O, ∀ x ∈ s, T x = f x := by
  classical
  let A := Algebra.adjoin ℂ O
  haveI : IsSimpleOrder (Submodule A V) := by
    refine ⟨fun N => ?_⟩
    have hst : ∀ T ∈ O, ∀ x ∈ N.restrictScalars ℂ, T x ∈ N.restrictScalars ℂ := by
      intro T hT x hx
      exact N.smul_mem (⟨T, Algebra.subset_adjoin hT⟩ : A) hx
    rcases hirr (N.restrictScalars ℂ) hst with h | h
    · left
      rw [← Submodule.restrictScalars_eq_bot_iff ℂ]
      exact h
    · right
      rw [← Submodule.restrictScalars_eq_top_iff ℂ]
      exact h
  haveI : IsSimpleModule A V := ⟨⟩
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun ψ x => by
        obtain ⟨c, hc⟩ := exists_smul_of_rank_le_aleph0 (R := A) hV ψ
        show f (ψ x) = ψ (f x)
        rw [hc, hc, f.map_smul] }
  obtain ⟨r, hr⟩ := jacobson_density F s
  exact ⟨r, r.2, fun x hx => (hr x hx).symm⟩
end GlobalTheory.ThK.Dbl.Dens
