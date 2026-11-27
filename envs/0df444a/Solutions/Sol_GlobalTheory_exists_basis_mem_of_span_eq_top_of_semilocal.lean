-- Prove2me | solution 1 for GlobalTheory.exists_basis_mem_of_span_eq_top_of_semilocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:27.094497+00:00
-- url     : https://prove2.me/submissions/59d7e059-6654-46f7-908a-3d58a9fd4c25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsBasisMemOfSpanEqTopOfSemilocal
import Theorems.Thm_GlobalTheory_SemilocalBasis_exists_linearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (A B M : Type) [CommRing A] [IsLocalRing A] [Infinite (IsLocalRing.ResidueField A)] [CommRing B] [Algebra A B] [Finite (MaximalSpectrum B)] [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] (n : ℕ) (_ : Module.Basis (Fin n) B M) (N : Submodule A M), (∀ m : MaximalSpectrum B, (IsLocalRing.maximalIdeal A).map (algebraMap A B) ≤ m.asIdeal) → Submodule.span B (N : Set M) = ⊤ → ∃ b : Module.Basis (Fin n) B M, ∀ i, b i ∈ N := by
  intro A B M _ _ _ _ _ _ _ _ _ _ n e N hm hN
  obtain ⟨v, hvN, hv⟩ := SemilocalBasis.exists_linearIndependent e N hm hN n le_rfl
  have hu : IsUnit (e.det v) := by
    by_contra hne
    obtain ⟨I, hI, hmem⟩ := exists_max_ideal_of_mem_nonunits hne
    letI := Ideal.Quotient.field I
    have h1 := hv ⟨I, hI⟩
    have h2 : IsUnit ((e.toMatrix v).map (Ideal.Quotient.mk I)) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp h1
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      ← Module.Basis.det_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hmem] at h2
    exact not_isUnit_zero h2
  obtain ⟨hli, hsp⟩ := e.is_basis_iff_det.mpr hu
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simpa using hvN i⟩
end GlobalTheory
