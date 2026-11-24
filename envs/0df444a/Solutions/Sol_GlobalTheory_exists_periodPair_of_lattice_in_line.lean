-- Prove2me | solution 1 for GlobalTheory.exists_periodPair_of_lattice_in_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:32.829132+00:00
-- url     : https://prove2.me/submissions/bbebf157-76f2-41ea-bfde-1892b5707f4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsPeriodPairOfLatticeInLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ), g = 1 → w ≠ 0 → DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ L : PeriodPair, ∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ := by
  intro g Λ w hg hw hdisc hspan
  subst hg
  have hw0 : w 0 ≠ 0 := by
    intro h
    apply hw
    funext j
    fin_cases j
    simpa using h

  obtain ⟨e, he⟩ : ∃ e : ℂ ≃L[ℝ] (Fin 1 → ℂ), ∀ z, e z = z • w := by
    let φ : ℂ →ₗ[ℝ] (Fin 1 → ℂ) :=
      { toFun := fun z => z • w
        map_add' := fun a b => add_smul a b w
        map_smul' := fun r z => by
          simp only [RingHom.id_apply]
          exact smul_assoc r z w }
    have hinj : Function.Injective φ := fun a b h => smul_left_injective ℂ hw h
    have hsurj : Function.Surjective φ := by
      intro y
      refine ⟨y 0 / w 0, ?_⟩
      funext j
      fin_cases j
      simp [φ, hw0]
    exact ⟨(LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, fun z => rfl⟩

  have : DiscreteTopology Λ := hdisc
  have : IsZLattice ℝ Λ := ⟨hspan⟩
  set Λ' := ZLattice.comap ℝ Λ e.toLinearMap with hΛ'
  have hrank : Module.finrank ℤ Λ' = 2 := by
    rw [ZLattice.rank ℝ Λ', Complex.finrank_real_complex]
  set b := Module.finBasisOfFinrankEq ℤ Λ' hrank with hb
  set bR := b.ofZLatticeBasis ℝ Λ' with hbR
  refine ⟨⟨bR 0, bR 1, ?_⟩, fun z => ?_⟩
  · have hv : ![bR 0, bR 1] = ⇑bR := by
      funext i
      fin_cases i <;> rfl
    rw [hv]
    exact bR.linearIndependent
  · have hr : ({bR 0, bR 1} : Set ℂ) = Set.range bR := by
      ext x
      simp [Fin.exists_fin_two, eq_comm]
    rw [PeriodPair.lattice]
    dsimp only
    rw [hr, hbR, Module.Basis.ofZLatticeBasis_span, ← SetLike.mem_coe, hΛ', ZLattice.coe_comap]
    simp [he]
end GlobalTheory
