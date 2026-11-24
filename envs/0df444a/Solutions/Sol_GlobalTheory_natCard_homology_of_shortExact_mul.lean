-- Prove2me | solution 1 for GlobalTheory.natCard_homology_of_shortExact_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:30:36.91244+00:00
-- url     : https://prove2.me/submissions/a1ebb05b-ff47-4aee-8217-7f2af5124d18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCardHomologyOfShortExactMul
import Theorems.Thm_GlobalTheory_natCard_eq_coker_mul_ker_of_exact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (p : ℕ) (C G : CochainComplex (ModuleCat.{0} ℤ) ℕ) (π : C ⟶ G) (hz : ((p : ℤ) • 𝟙 C) ≫ π = 0), (ShortComplex.mk ((p : ℤ) • 𝟙 C) π hz).ShortExact → ∀ n : ℕ, Nat.card (G.homology n) = Nat.card ((C.homology n) ⧸ LinearMap.range ((p : ℤ) • (LinearMap.id : C.homology n →ₗ[ℤ] C.homology n))) * Nat.card (LinearMap.ker ((p : ℤ) • (LinearMap.id : C.homology (n + 1) →ₗ[ℤ] C.homology (n + 1)))) := by
  intro p C G π hz hS n
  have hmul0 : ∀ k, HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k = (p : ℤ) • 𝟙 _ := by
    intro k
    have := (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) k).map_zsmul
      (f := 𝟙 C) (r := (p : ℤ))
    rw [CategoryTheory.Functor.map_id] at this
    exact this
  have hmul : ∀ k, (HomologicalComplex.homologyMap ((p : ℤ) • 𝟙 C) k).hom
      = (p : ℤ) • (LinearMap.id : C.homology k →ₗ[ℤ] C.homology k) := by
    intro k
    rw [hmul0]
    ext x
    simp
  have e2 := (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have e3 := (hS.homology_exact₃ n (n+1) rfl).moduleCat_range_eq_ker
  have e1 := (hS.homology_exact₁ n (n+1) rfl).moduleCat_range_eq_ker
  dsimp only at e1 e2 e3
  rw [hmul] at e1 e2
  exact natCard_eq_coker_mul_ker_of_exact _ _ _ _ e2 e3 e1
end GlobalTheory
