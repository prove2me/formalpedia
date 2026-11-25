-- Prove2me | solution 1 for GlobalTheory.SecGrowth.finite_secM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:16.258456+00:00
-- url     : https://prove2.me/submissions/ea81c723-75b0-49b5-832f-ab3c07c12037

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
import Theorems.Thm_GlobalTheory_SecGrowth_finite_of_not_linearIndependent
import Theorems.Thm_GlobalTheory_PowSec_appLE_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_linComb


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
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
namespace GlobalTheory.SecGrowth
theorem _root_.solution {K : Type} [Field K] (P : PolAV (Spec (CommRingCat.of K)))
    (hfin : ∀ M : LB P.A.left, M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M,
      ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧
        ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) (a : ℤ) :
    Module.Finite Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤)
      (SecM P.A P.L a (baseOver (Spec (CommRingCat.of K)))) := by
  let T : Over (Spec (CommRingCat.of K)) := baseOver (Spec (CommRingCat.of K))
  obtain ⟨n, hn⟩ := hfin (LB.LinComb P.L (K := PUnit) (fun _ => 𝟙 P.A.left) (fun _ => a))
    (LB.isLB_linComb P.isLB _ _)
  refine finite_of_not_linearIndependent (isField_of_isIntegral_of_subsingleton (Spec (CommRingCat.of K))) n
    fun b hb => ?_
  let ρ : P.A ⟶ T ⊗ P.A := lift (Over.homMk P.A.hom (Category.comp_id _)) (𝟙 _)
  have ρ₂ : ρ.left ≫ (snd T P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_snd _ _ : ρ ≫ _ = _)
  have ρ₁ : ρ.left ≫ (fst T P.A).left = P.A.hom := congrArg (fun q => q.left) (lift_fst _ _ : ρ ≫ _ = _)
  have ρ₃ : (snd T P.A).left ≫ ρ.left = 𝟙 _ := by
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₁).trans (pullback.condition.symm.trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ρ₂).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
  haveI : IsIso ρ.left := ⟨_, ρ₂, ρ₃⟩
  obtain ⟨c, hc, ha⟩ := hn fun i => PowSec.down P.L (snd T P.A).left ρ.left ρ₂ a (SecM.toSec P.A (b i))
  have h0 : ∑ i, (show Γ(T.left, ⊤) from c i) • b i = 0 := by
    refine Subtype.ext (funext fun j => ?_)
    obtain ⟨k, rfl⟩ : ∃ k, j = fun _ => k := ⟨j 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine PowSec.appLE_injective ρ.left _ _ (PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)) ?_
    refine Eq.trans ?_ ((ha (fun _ => k)).trans (map_zero _).symm)
    rw [Submodule.coe_sum]
    refine (congrArg _ (Finset.sum_apply _ _ _)).trans ?_
    refine (map_sum (ρ.left.appLE _ _ (PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).hom
      _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
    refine (map_mul _ (liftHom P.A _ (c i)) ((b i).1 fun _ => k)).trans (congrArg₂ (· * ·) ?_ rfl)
    have h1 := (Scheme.Hom.appLE_comp_appLE ρ.left (fst T P.A).left ⊤ _ _ (fun _ _ => trivial)
      (PowSec.chart_eq P.L (snd T P.A).left ρ.left ρ₂ (fun _ => k)).le).trans
      (PowSec.appLE_congr ρ₁ ⊤ _ _ (fun _ _ => trivial))
    exact congrArg (fun φ => φ.hom (c i)) h1
  exact hc (funext fun i => Fintype.linearIndependent_iff.1 hb _ h0 i)
end GlobalTheory.SecGrowth
