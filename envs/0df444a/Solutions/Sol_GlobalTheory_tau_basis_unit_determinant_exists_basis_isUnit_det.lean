-- Prove2me | solution 1 for GlobalTheory.tau_basis_unit_determinant.exists_basis_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:29:30.623335+00:00
-- url     : https://prove2.me/submissions/16976751-98cf-4e00-b874-cbf7bdacb3a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitDeterminantBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TauBasisUnitDeterminant
import Theorems.Thm_GlobalTheory_UnitDeterminantBasis_det_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory GlobalTheory.tau_basis_unit_determinant
namespace GlobalTheory.tau_basis_unit_determinant
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] (O : Type) [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[p] O] (w : PlaceU p OE) (t : Fin w.n → (OE →+* O)),
    (∀ j, t j ∈ Emb (O := O) w.e) →
    (∀ j j', (∀ x, t j x - t j' x ∈ maximalIdeal O) → j = j') →
    ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
      IsUnit (Matrix.det (Matrix.of fun i j => tauExt (t j) (b i : ℤ_[p] ⊗[ℤ] OE))) := by
  intro p _ OE _ _ _ O _ _ _ w t ht hsep
  let b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) :=
    Module.finBasisOfFinrankEq _ _ rfl
  refine ⟨b, ?_⟩
  by_contra hx
  have hxM := (mem_maximalIdeal _).2 hx
  let T : Fin w.n → (TensorProduct ℤ ℤ_[p] OE →ₐ[ℤ_[p]] O ⧸ maximalIdeal O) := fun j =>
    (Ideal.Quotient.mkₐ ℤ_[p] (maximalIdeal O)).comp (tauExt (t j))
  refine GlobalTheory.UnitDeterminantBasis.det_ne_zero b T ?_ ?_ ?_
  · intro j j' h
    refine hsep _ _ fun a => ?_
    have h1 := DFunLike.congr_fun h (1 ⊗ₜ a)
    rw [← Ideal.Quotient.eq]
    simpa [T, tauExt] using h1
  · intro j
    have h1 : tauExt (t j) w.e = 1 := ht j
    simp only [T, AlgHom.comp_apply, h1, map_one]
  · have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hxM
    rw [RingHom.map_det] at h1
    exact h1
end GlobalTheory.tau_basis_unit_determinant
