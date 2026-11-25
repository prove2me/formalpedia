-- Prove2me | solution 1 for GlobalTheory.jetCoord_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:36.149403+00:00
-- url     : https://prove2.me/submissions/d8c2a986-dbc7-4a7a-b752-98898dd70adc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetPointAddSqZeroEqProdMulTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_JetChartCoordinatesUniqueCommGroup
import Theorems.Thm_GlobalTheory_jetCoord_eq_of_sub_mem
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open SqZero
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (hG : Smooth G.hom) (d : ℕ) (v : Fin d → (epsR R ⟶ G)) (hv : IsLieBasis v)
    (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hx₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m)
    (hx₂ : ∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1)
    (hx₃ : ∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j)
    (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ)
    (hN : (RingHom.ker aug) ^ (m + 1) = ⊥) (ψ ψ' : JetR R (Fin d) m →ₐ[R] A)
    (hψ : aug.comp ψ = jetAug R (Fin d) m) (hψ' : aug.comp ψ' = jetAug R (Fin d) m)
    (h : spMap ψ ≫ x m = spMap ψ' ≫ x m) : ψ = ψ' := by
  set N := RingHom.ker aug with hNdef
  have main : ∀ k j, ψ' (zR m j) - ψ (zR m j) ∈ N ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      intro j
      rw [zero_add, pow_one, hNdef, RingHom.mem_ker, map_sub, ← AlgHom.comp_apply,
        ← AlgHom.comp_apply, hψ, hψ', sub_self]
    | succ k ih =>
      let q : A →ₐ[R] A ⧸ N ^ (k + 1 + 1) := Ideal.Quotient.mkₐ R _
      have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R _
      let aug' : (A ⧸ N ^ (k + 1 + 1)) →ₐ[R] R := Ideal.Quotient.liftₐ _ aug
        (fun a ha => Ideal.pow_le_self (by omega) ha)
      have haug : aug'.comp q = aug := AlgHom.ext fun _ => rfl
      have hker : RingHom.ker aug' = N.map q := by
        apply le_antisymm
        · intro a ha
          obtain ⟨b, rfl⟩ := hq a
          exact Ideal.mem_map_of_mem _ ha
        · exact Ideal.map_le_iff_le_comap.2 fun a ha => ha
      have e := jetCoord_eq_of_sub_mem hG hv hx₁ hx₂ hx₃ aug' ((N ^ (k + 1)).map q)
        (by rw [hker, ← Ideal.map_mul, ← pow_succ]; exact Ideal.map_quotient_self _)
        (by rw [hker]; exact Ideal.map_mono (Ideal.pow_le_self (by omega)))
        (q.comp ψ) (q.comp ψ') (by rw [← AlgHom.comp_assoc, haug, hψ])
        (by rw [← AlgHom.comp_assoc, haug, hψ'])
        (fun j => by
          rw [AlgHom.comp_apply, AlgHom.comp_apply, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih j))
        (by rw [← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, h])
      intro j
      exact Ideal.Quotient.eq.1 (AlgHom.congr_fun e (zR m j)).symm
  refine jet_ext fun j => ?_
  have := main m j
  rw [hN, Ideal.mem_bot] at this
  exact (sub_eq_zero.1 this).symm
end GlobalTheory
