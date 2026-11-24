-- Prove2me | solution 1 for GlobalTheory.HopfQuot.exists_integrals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:11:21.854959+00:00
-- url     : https://prove2.me/submissions/233eb4ca-4919-4ac4-9075-2c4652100b32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_lam_integral
import Theorems.Thm_GlobalTheory_HopfQuot_sum_lam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (R Λ : Type*) [CommRing R] [CommRing Λ] [HopfAlgebra R Λ]
    [Module.Finite R Λ] [Module.Projective R Λ] :
    ∃ (n : ℕ) (l : Fin n → Λ →ₗ[R] R) (T : Fin n → Λ),
      (∀ k x, ev Λ (l k) (Coalgebra.comul x) = algebraMap R Λ (l k x)) ∧
      ∀ x, ∑ k, l k (T k * x) = Coalgebra.counit (R := R) x := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R Λ
  let e : Fin n → Λ := fun i => p (Pi.single i 1)
  let c : Fin n → Λ →ₗ[R] R := fun i => LinearMap.proj i ∘ₗ s
  have h : ∀ m, ∑ i, c i m • e i = m := by
    intro m
    have h1 : p (s m) = m := LinearMap.congr_fun hps m
    conv_rhs => rw [← h1, pi_eq_sum_univ' (s m)]
    simp [c, e, map_sum]
  exact ⟨n, fun k => lam e c (c k), fun k => HopfAlgebra.antipode R (e k),
    fun k x => lam_integral e c h _ x, sum_lam e c h⟩
end GlobalTheory.HopfQuot
