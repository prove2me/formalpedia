-- Prove2me | solution 1 for GlobalTheory.UnitDeterminantBasis.exists_basis_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:55.809933+00:00
-- url     : https://prove2.me/submissions/a8233bda-46cf-46de-b561-0c511645fb4f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitDeterminantBasis
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
open ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.UnitDeterminantBasis
namespace GlobalTheory.UnitDeterminantBasis
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R], v.Integers R → (∀ σ σ' : OE →+* R, (∀ a : OE, v (algebraMap R C (σ a - σ' a)) < 1) → σ = σ') → ∀ (w : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.PlaceU p OE) (t : Fin w.n ≃ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e), ∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)), IsUnit (Matrix.det (Matrix.of fun i j => ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt ((t j : ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.Emb (O := R) w.e) : OE →+* R) (b i : TensorProduct ℤ ℤ_[p] OE))) := by
  intro p _ OE _ _ _ C _ v R _ _ _ hv hsep w t
  let b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)) :=
    Module.finBasisOfFinrankEq _ _ rfl
  refine ⟨b, ?_⟩
  by_contra hx
  obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits hx
  have hMp : M.IsPrime := hM.isPrime
  let T : Fin w.n → (TensorProduct ℤ ℤ_[p] OE →ₐ[ℤ_[p]] R ⧸ M) := fun j =>
    (Ideal.Quotient.mkₐ ℤ_[p] M).comp (AvDefs.tauExt ((t j : AvDefs.Emb (O := R) w.e) : OE →+* R))
  refine det_ne_zero b T ?_ ?_ ?_
  · intro j j' h
    apply t.injective
    apply Subtype.ext
    refine hsep _ _ fun a => ?_
    have h1 := DFunLike.congr_fun h (1 ⊗ₜ a)
    have h2 : ((t j : AvDefs.Emb (O := R) w.e) : OE →+* R) a -
        ((t j' : AvDefs.Emb (O := R) w.e) : OE →+* R) a ∈ M := by
      rw [← Ideal.Quotient.eq]
      simpa [T, AvDefs.tauExt] using h1
    refine lt_of_le_of_ne (hv.map_le_one _) fun h3 => ?_
    exact hM.ne_top (M.eq_top_of_isUnit_mem h2 (hv.isUnit_iff_valuation_eq_one.2 h3))
  · intro j
    have h1 : AvDefs.tauExt ((t j : AvDefs.Emb (O := R) w.e) : OE →+* R) w.e = 1 := (t j).2
    simp only [T, AlgHom.comp_apply, h1, map_one]
  · have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hxM
    rw [RingHom.map_det] at h1
    exact h1
end GlobalTheory.UnitDeterminantBasis
