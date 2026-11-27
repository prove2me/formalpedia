-- Prove2me | solution 1 for GlobalTheory.AdjRead.exists_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:36:59.965231+00:00
-- url     : https://prove2.me/submissions/478e493c-86dc-400e-8cb8-29eb537f5966

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGenRosati
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBaseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AbelianHolomorphicFrameReadingConstOfFormsCancelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInvStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingPullbackPeriodRigidStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsAdjReadingOne
import Theorems.Thm_GlobalTheory_AnValGenCorr_val_inv
import Theorems.Thm_GlobalTheory_NormRos_normRos_of_lbIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
private theorem padd_lemma {T : Over S} (a b : T ⟶ A) : padd A a b = a * b := rfl
private theorem pzero_eq_one_cusp_form_evaluations {T : Over S} : pzero A T = 1 := rfl
variable {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
end GlobalTheory.AdjRead
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AdjRead
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
namespace GlobalTheory.AdjRead
theorem _root_.solution {L : LB A.left} (hL : L.IsLB) (f f' : A ⟶ A) [IsMonHom f] [IsMonHom f']
    (H : LBIso (cubeLB A ![fst A A ≫ f, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ f'] L)) :
    ∃ u : LB.Gen (LB.LinComb L (adφ f f') adε), u.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left) (LB.oneGen L) := by
  obtain ⟨⟨u0, hu0, hn0⟩, -⟩ := GlobalTheory.NormRos.normRos_of_lbIso S A L hL f f' H
  have hinv := ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen L _ _ u0 hu0
  have hF : FormEq (rosatiφ A f f') (fun k => -rosatiε k) (adφ f f') adε := by
    intro U _ h
    have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
    rw [Fintype.prod_sum_type]
    simp only [adφ, adε, Sum.elim_inl, Sum.elim_inr]
    rw [← Equiv.prod_comp Equiv.ulift.symm, ← Equiv.prod_comp Equiv.ulift.symm (fun I => h (cub _ I) ^ (-cε 2 I)), hu]
    rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_singleton, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
      Finset.prod_insert (by decide), Finset.prod_singleton]
    simp [Fin.prod_univ_succ, rosatiφ, rosatiε, cub, psum, List.finRange_succ, padd_lemma, pzero_eq_one_cusp_form_evaluations, cε, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨t, ht, hv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hL hF _ hinv
  refine ⟨t, ht, ?_⟩
  have hz : (lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A)).left = (A ⊗ A).hom ≫ zero2 A := by
    have h1 : lift (1 : A ⊗ A ⟶ A) (1 : A ⊗ A ⟶ A) = toUnit (A ⊗ A) ≫ lift η η := by
      rw [comp_lift]; rfl
    rw [h1, Over.comp_left]
    congr 1
  apply ReciprocityTheory.ChartRestriction.G.Geo.Tor.corr_of_val hL
  intro y J hJ
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_one, hv _ _ _ _ hJ,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_inv, Category.id_comp, hz, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ,
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ hn0, ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_one, inv_one]
end GlobalTheory.AdjRead
