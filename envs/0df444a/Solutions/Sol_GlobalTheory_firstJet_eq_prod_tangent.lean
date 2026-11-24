-- Prove2me | solution 1 for GlobalTheory.firstJet_eq_prod_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:07.627032+00:00
-- url     : https://prove2.me/submissions/3f05d0fc-d366-428b-a10c-c4244fa85ba3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FirstJetEqProdTangent
import Theorems.Thm_GlobalTheory_firstJet_eq_aug_add_sum
import Theorems.Thm_GlobalTheory_SqZero_comp_lieExp
import Theorems.Thm_GlobalTheory_SqZero_epsTo_zero_comp
import Theorems.Thm_GlobalTheory_SqZero_expBij
import Theorems.Thm_GlobalTheory_SqZero_mem_redKer_of_section
import Theorems.Thm_GlobalTheory_SqZero_scaleD_eq
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleD_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id


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
open SqZero TrivSqZeroExt
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)),
    IsLieBasis v → ∀ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G),
    (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) →
    (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) →
    ∀ (A : Type) [CommRing A] [Algebra R A] (ψ : JetR R (Fin d) 1 →ₐ[R] A)
      (e : Fin d → (DualNumber R →ₐ[R] A)), (∀ j, e j (TrivSqZeroExt.inr 1) = ψ (zR 1 j)) →
      spMap ψ ≫ x 1 = ∏ j, (spMap (e j) ≫ v j : sp (R₀ := R) A ⟶ G) := by
  intro R _ G _ _ hG d v hv x hx0 hx1 A _ _ ψ e he
  have haug : spMap (jetAug R (Fin d) 1) ≫ x 1 = 1 := by
    have e : jetAug R (Fin d) 1 = (jetAug R (Fin d) 0).comp (jetZeroR R (Fin d) 1) :=
      jet_ext fun j => by rw [AlgHom.comp_apply, jetAug_zR]; exact (jetAug_zR (R := R) 0 j).symm
    rw [e, ← spMap_comp, Category.assoc, hx0 1, comp_one']
  obtain ⟨c, hc, hcJ, hxc⟩ := (expBij _ hv _ (ker_jetAug_pow (R := R) (Fin d) 1)).2 (x 1)
    (mem_redKer_of_section _ (Algebra.ofId R _) (fun a => (jetAug R (Fin d) 1).commutes a) haug)
  have hs : ∀ j i : Fin d, dualLift (Pi.single j (1 : R)) (c i) =
      inr ((Pi.single j (1 : R) : Fin d → R) i) := fun j => by
    have h₁ := hx1 j
    rw [hxc, comp_lieExp] at h₁
    have h₂ : lieExp v (fun i => (inr ((Pi.single j (1 : R) : Fin d → R) i) : DualNumber R))
        (fun _ => inr_mul_inr _ _ _) = v j := by
      rw [lieExp, Finset.prod_eq_single j]
      · rw [← scaleD_eq, Pi.single_eq_same, scaleD_one, spMap_id]
        exact Category.id_comp _
      · intro i _ hi
        exact epsTo_zero_comp ((isTan_iff _).2 (hv.1 i)) _
          (by rw [Pi.single_eq_of_ne hi, inr_zero]) _
      · exact fun h => absurd (Finset.mem_univ j) h
    have h₃ : ∀ i, dualLift (Pi.single j (1 : R)) (c i) ∈ RingHom.ker (fstD R) := fun i => by
      rw [RingHom.mem_ker, ← AlgHom.comp_apply, fstD_comp_dualLift]
      exact hcJ i
    exact congrFun ((expBij (DualNumber R) hv (RingHom.ker (fstD R)) kerD_sq).1
      (fun i => dualLift (Pi.single j (1 : R)) (c i))
      (fun i => inr ((Pi.single j (1 : R) : Fin d → R) i)) h₃ (fun i => inr_mem_kerD _) _ _
      (h₁.trans h₂.symm))
  have hcz : ∀ i, c i = zR 1 i := fun i => by
    rw [firstJet_eq_aug_add_sum (c i), (hcJ i : jetAug R (Fin d) 1 (c i) = 0), map_zero, zero_add,
      Finset.sum_eq_single i]
    · rw [hs, snd_inr, Pi.single_eq_same, map_one, _root_.one_mul]
    · intro j _ hj
      rw [hs, snd_inr, Pi.single_eq_of_ne hj.symm, map_zero, zero_mul]
    · exact fun h => absurd (Finset.mem_univ i) h
  rw [hxc, comp_lieExp, lieExp]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 2
  exact DualNumber.algHom_ext (by rw [epsTo_eps, hcz]; exact (he j).symm)
end GlobalTheory
