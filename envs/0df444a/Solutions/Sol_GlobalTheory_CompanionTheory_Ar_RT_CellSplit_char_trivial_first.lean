-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.RT.CellSplit.char_trivial_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:25:18.653783+00:00
-- url     : https://prove2.me/submissions/c9da0905-310f-4a4b-bef5-d319039c5979

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_glPr_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_lift_diag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_uLift_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_pr_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_isUnit_det_dbl
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_Siegel_char_trivial_artinian
import Theorems.Thm_GlobalTheory_WeilM_isLagr_diagCols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
section Lift
variable {S E₁ E₂ : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂)
variable {n : Type} [DecidableEq n]
variable [Fintype n]
end Lift
section Unitary
variable {k R S E₁ E₂ : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [Algebra k E₁] [CommRing E₂]
  (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (s : S ≃+* E₁ × E₂)
  (hc1 : ∀ x, (s (c x)).1 = c₁ (s x).1) (hc2 : ∀ x, (s (c x)).2 = c₂ (s x).2)
variable {β : Type} [Fintype β] [DecidableEq β] (J : Matrix β β S)
end Unitary
private theorem snd_lift_sub_one_apply_eq_zero {S E₁ E₂ n : Type} [CommRing S] [CommRing E₁] [CommRing E₂] [DecidableEq n]
    (s : S ≃+* E₁ × E₂) (X : Matrix n n E₁) (i j : n) : (s ((lift s X - 1) i j)).2 = 0 := by
  by_cases h : i = j
  · subst h
    simp [lift]
  · simp [lift, Matrix.one_apply_ne h]
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
end

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM
namespace GlobalTheory.CompanionTheory.Ar.RT.CellSplit
theorem _root_.solution : ∀ (k : Type) [Field k] [CharZero k] (R S E₁ E₂ : Type) [CommRing R] [CommRing S] [Algebra R S] [CommRing E₁] [IsArtinianRing E₁] [Algebra k E₁] [CommRing E₂] (c : S →ₐ[R] S) (c₁ : E₁ →ₐ[k] E₁) (c₂ : E₂ →+* E₂) (ξ₁ : E₁) (s : S ≃+* E₁ × E₂), IsUnit ξ₁ → c₁ ξ₁ = -ξ₁ → (∀ x, c₁ (c₁ x) = x) → (∀ x, (s (c x)).1 = c₁ (s x).1) → (∀ x, (s (c x)).2 = c₂ (s x).2) → ∀ (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β S), IsUnit J.det → ∀ lam : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J) →* ℂˣ, (∀ (p : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J)) (t : GL β S), (∀ i j, (s ((((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → (∀ i j, (s (((t : Matrix β β S) - 1) i j)).2 = 0) → ((p : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) * GlobalTheory.WeilM.diagCols β = GlobalTheory.WeilM.diagCols β * (t : Matrix β β S) → lam p = 1) → ∀ g : GlobalTheory.WeilM.UG c (GlobalTheory.WeilM.dbl J), (∀ i j, (s ((((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S) - 1) i j)).2 = 0) → lam g = 1 := by
  intro k _ _ R S E₁ E₂ _ _ _ _ _ _ _ c c₁ c₂ ξ₁ s hξ hcξ hinv hc1 hc2 β _ _ J hdet lam hlam g hg
  haveI : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
  have hdet₁ : IsUnit (J.map (pr₁ s)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map (pr₁ s)
  have hP : ∀ (p : UG c₁ (dbl (J.map (pr₁ s)))) (t : GL β E₁),
      ((p : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁) * diagCols β = diagCols β * (t : Matrix β β E₁) →
        (lam.comp (uLift c c₁ c₂ s hc1 hc2 J)) p = 1 := by
    intro p t hpt
    show lam (uLift c c₁ c₂ s hc1 hc2 J p) = 1
    refine hlam (uLift c c₁ c₂ s hc1 hc2 J p) (glLift s t) ?_ ?_ ?_
    · intro i j
      rw [uLift_coe]
      exact snd_lift_sub_one_apply_eq_zero s _ i j
    · intro i j
      rw [glLift_coe]
      exact snd_lift_sub_one_apply_eq_zero s _ i j
    · rw [uLift_coe, glLift_coe]
      exact lift_diag s _ _ hpt
  have hlam1 := GlobalTheory.CompanionTheory.Ar.RT.Siegel.char_trivial_artinian k E₁ c₁ ξ₁ (β ⊕ β) β (dbl (J.map (pr₁ s)))
    (diagCols β) hξ hcξ hinv (isUnit_det_dbl _ hdet₁) (GlobalTheory.WeilM.isLagr_diagCols c₁ (J.map (pr₁ s)))
    (lam.comp (uLift c c₁ c₂ s hc1 hc2 J)) hP
  have hG2 : ((g : GL (β ⊕ β) S) : Matrix (β ⊕ β) (β ⊕ β) S).map (pr₂ s) = 1 := by
    ext i j
    have hij := hg i j
    rw [Matrix.map_apply, pr₂_apply]
    rw [Matrix.sub_apply, map_sub, Prod.snd_sub, sub_eq_zero] at hij
    rw [hij]
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  have hg1 : uLift c c₁ c₂ s hc1 hc2 J ⟨glPr s (g : GL (β ⊕ β) S), pr_mem c c₁ s hc1 J g⟩ = g := by
    apply Subtype.ext
    apply Units.ext
    rw [uLift_coe]
    show lift s ((glPr s (g : GL (β ⊕ β) S) : GL (β ⊕ β) E₁) : Matrix (β ⊕ β) (β ⊕ β) E₁) = _
    rw [glPr_coe]
    apply mat_ext s
    · rw [lift_map₁]
    · rw [lift_map₂, hG2]
  rw [← hg1]
  exact DFunLike.congr_fun hlam1 _
end GlobalTheory.CompanionTheory.Ar.RT.CellSplit
