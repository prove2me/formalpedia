-- Prove2me | solution 1 for MasulloGRH.bounded_lifting_of_stage_factorizations
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-20T22:39:06.08419+00:00
-- url     : https://prove2.me/submissions/461fe44e-9b7e-483b-820e-5c66fc284ba8

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_bounded_sets_strict_inductive_limit

set_option autoImplicit false
open Set
open MasulloGRH

/-- The bounded-set lifting assembly used at the end of Corollary C.1.5.13. -/
theorem solution
    (E Q : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup Q] [Module ℂ Q] [TopologicalSpace Q]
    (hQ : IsHLCS Q) (Y : ℕ → Submodule ℂ Q) (hmono : Monotone Y)
    (hexh : ∀ y : Q, ∃ n, y ∈ Y n) (hcl : ∀ n, IsClosed (Y n : Set Q))
    (htop : ‹TopologicalSpace Q› =
      sInf {t | IsLocallyConvexTopology Q t ∧ ∀ n, @Continuous (Y n) Q _ t Subtype.val})
    (F P : ℕ → Type*) [∀ n, AddCommGroup (F n)] [∀ n, Module ℂ (F n)]
    [∀ n, TopologicalSpace (F n)] [∀ n, AddCommGroup (P n)] [∀ n, Module ℂ (P n)]
    [∀ n, TopologicalSpace (P n)]
    (q : E → Q) (j : ∀ n, F n →L[ℂ] E) (p : ∀ n, F n → P n)
    (r : ∀ n, P n → Q) (v : ∀ n, Y n →L[ℂ] P n)
    (hlift : ∀ n, LiftsBoundedSets (p n))
    (hcomm : ∀ n x, q (j n x) = r n (p n x))
    (hfactor : ∀ n y, r n (v n y) = (y : Q)) :
    LiftsBoundedSets q := by
  intro B hB
  obtain ⟨n, C, hC, hBC⟩ :=
    (MasulloGRH.bounded_sets_strict_inductive_limit Q hQ Y hmono hexh hcl htop B).mp hB
  obtain ⟨D, hD, hCD⟩ := hlift n (v n '' C) (hC.image (v n))
  refine ⟨j n '' D, hD.image (j n), ?_⟩
  rintro b hb
  rw [hBC] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  obtain ⟨x, hx, hpx⟩ := hCD ⟨y, hy, rfl⟩
  refine ⟨j n x, ⟨x, hx, rfl⟩, ?_⟩
  rw [hcomm, hpx, hfactor]
