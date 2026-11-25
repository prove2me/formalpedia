-- Prove2me | solution 1 for GlobalTheory.BoxDetUnique.box_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:08:46.671793+00:00
-- url     : https://prove2.me/submissions/b5e1cec8-6df0-4c71-ba3c-c7ea81a85933

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsBoxSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsSquareDetComparisonEqMulDetPowOfBasisChange
import Theorems.Thm_GlobalTheory_BoxDetUnique_isProper_powObj
import Theorems.Thm_GlobalTheory_BoxDetUnique_exists_boxSec
import Theorems.Thm_GlobalTheory_BoxDetUnique_gs_cst
import Theorems.Thm_GlobalTheory_KuennethOne_appLE_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_appLE
import Theorems.Thm_GlobalTheory_KuennethOne_rs_rs
import Theorems.Thm_GlobalTheory_KuennethOne_rs_self
import Theorems.Thm_GlobalTheory_T_section_lin_comb_fiber_product_separated
import Theorems.Thm_P2M_GlobalTheory_BoxDetUnique_gs_sum__a1ab71d3ee53
import Theorems.Thm_P2M_GlobalTheory_BoxDetUnique_gs_zero__4dae196bb222
import Theorems.Thm_P2M_GlobalTheory_SectionsProduct_gs_sum__5d885260760f
import Theorems.Thm_P2M_GlobalTheory_SectionsProduct_gs_zero__6e6cf73bee24
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.KuennethOne.appLE_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_appLE
attribute [local simp] GlobalTheory.KuennethOne.rs_rs
attribute [local simp] GlobalTheory.KuennethOne.rs_self



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.BoxDetUnique
namespace GlobalTheory.BoxDetUnique
theorem _root_.solution {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left}
    (hL : L.IsLB) {m : ℤ} {N : ℕ} (b : Fin N → LB.Sec (pw L m))
    (hb : ∀ c : Fin N → K, (∀ i, ∑ k, cst A.hom (L.U i) (c k) * (show Γ(A.left, L.U i) from (b k).f i) = 0) → c = 0) :
    ∀ (n : ℕ) (q : (Fin n → Fin N) → K), (∀ (y : (Out.powObj A n).left) J, Good L y J →
      ∑ I, kv (Out.powObj A n).hom y (q I) * ∏ c, gs (Out.powPr A c).left y (L.U (J (Out.powPr A c).left))
        ((b (I c)).f (J (Out.powPr A c).left)) = 0) → q = 0 := by
  intro n
  induction n with
  | zero =>
    intro q hq
    let y : (Out.powObj A 0).left := IsLocalRing.closedPoint K
    choose J hJ using fun χ : (Out.powObj A 0).left ⟶ A.left => exists_chart hL (χ y)
    have := hq y J hJ
    rw [Fintype.sum_unique, Fintype.prod_empty, _root_.mul_one, map_eq_zero] at this
    exact funext fun I => (congrArg q (Subsingleton.elim _ _)).trans this
  | succ n ih =>
    intro q hq
    haveI := hA.proper
    haveI := isProper_powObj A hA n
    choose a ha using fun i : Fin N => exists_boxSec (L := L) (fun _ : Unit => 𝟙 A.left) A.hom (fun _ : Unit => (1 : K))
      (fun _ _ => b i)
    choose d hd using fun i : Fin N => exists_boxSec (L := L) (fun c : Fin n => (Out.powPr A c).left) (Out.powObj A n).hom
      (fun I : Fin n → Fin N => q (Fin.cons i I)) (fun I c => b (I c))
    have H := (GlobalTheory.T.section_lin_comb_fiber_product_separated K _ L hL A (Out.powObj A n) Unit (Fin n) (fun _ => 𝟙 A.left) (fun _ => m)
      (fun c => (Out.powPr A c).left) (fun _ => m)).2 N a d (fun c hc => hb c fun i => fn_ext fun y hy => by
        have hy' : (𝟙 A.left : A.left ⟶ A.left) y ∈ LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i) :=
          Set.mem_iInter.2 fun _ => hy
        have := congrArg (gs (𝟙 A.left) y (LB.wchart L (fun _ : Unit => 𝟙 A.left) (fun _ => i))) (hc (fun _ => i))
        refine Eq.trans ?_ (((gs_sum' _ y _ hy' _ _).symm.trans this).trans
          ((gs_zero' _ y _ hy').trans (gs_zero' _ y _ hy).symm))
        refine (gs_sum' (𝟙 A.left) y _ hy _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
        refine (gs_mul (𝟙 A.left) y _ hy _ _).trans (Eq.trans ?_ (gs_mul (𝟙 A.left) y _ hy' _ _).symm)
        refine congrArg₂ (· * ·) ((gs_cst A.hom _ y _ hy _).trans (gs_cst A.hom _ y _ hy' _).symm) ?_
        rw [ha k _ _ y _ hy', Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id])
      (fun z J hJ => by
        refine Eq.trans ?_ (hq z J hJ)
        rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Fin N).sum_comp, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => ?_
        refine (congrArg₂ (· * ·) (ha i _ _ z _ (hJ.mem _ _)) (hd i _ _ z _ (hJ.mem _ _))).trans ?_
        rw [Fintype.sum_unique, Fintype.prod_unique, map_one, _root_.one_mul, Category.comp_id, Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Fin.prod_univ_succ, mul_left_comm, Over.w (snd A (Out.powObj A n))]
        rfl)
    funext I
    have := ih (fun I' => q (Fin.cons (I 0) I')) (fun y J hJ => by
      have h1 := hd (I 0) _ (𝟙 _) y (fun c => J (Out.powPr A c).left) (Set.mem_iInter.2 fun c => hJ _)
      have h0 := h1.symm.trans ((congrArg (gs (𝟙 _) y _) (H _ _)).trans
        (gs_zero' _ y _ (Set.mem_iInter.2 fun c => hJ _)))
      simpa only [Category.id_comp] using h0)
    have h2 := congrFun this (Fin.tail I)
    rwa [Fin.cons_self_tail] at h2
end GlobalTheory.BoxDetUnique
