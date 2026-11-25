-- Prove2me | solution 1 for GlobalTheory.cubical_symmetry_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:29:56.757132+00:00
-- url     : https://prove2.me/submissions/89bdf7e0-c124-4d1b-91cb-8c0f7aa28937

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Theorems.Thm_GlobalTheory_CubTransport_exists_pmaps
import Theorems.Thm_GlobalTheory_CubTransport_val_pmaps
import Theorems.Thm_GlobalTheory_CubTransport_isCub_of_twist
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_cubeMap_comp_proj_three
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_hom_ext_triple
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open CubTransport ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
theorem _root_.solution : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (hgp : Geo.Tor.IsGrpPullback G' G f Ψ) (L : RigLB G) (L' : RigLB G') (wL : LB.Iso L'.L (L.L.pull Ψ)) (he : eSec G' ≫ Ψ = f ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) → ∀ (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) → ∃ (c' : CubicalStr G' L') (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen ∧ LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ s' (eSec G')) (LB.oneGen L'.L) ∧ Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (Geo.Tor.cubeMapOf hgp).F3 ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' s Ψ := by
  intro S S' f G _ _ G' _ _ Ψ hgp L L' wL he hw _ c s hs hs1
  have hw' := (isGen_iff wL).1 hw
  have good : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good L.L z J := fun {Z} z => by
    choose I hI using fun χ : Z ⟶ G.left => exists_chart L.isLB (χ z)
    exact ⟨I, hI⟩
  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ Ψ = (cubeMapOf hgp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf hgp).psum_comm I.down
  obtain ⟨t', ht', Ht⟩ := exists_pmaps hw' L.isLB L'.isLB (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (cubeMapOf hgp).F3 hc c.t c.isGen
  have hι : (ι[G']).left ≫ Ψ = Ψ ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom hgp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ Ψ) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ Ψ = Ψ ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', Hs⟩ := exists_pmaps hw' L.isLB L'.isLB Ψ hc₂ s hs
  refine ⟨cubicalOfVal t' ht' fun T z J' hJ' => ?_, s', hs', corr_of_val L'.isLB fun y J' hJ' => ?_, Ht, Hs⟩
  · obtain ⟨J, hJ⟩ := good z
    refine isCub_of_twist (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ) (pushHom hgp T)
      (fun x => gw wL x.left z (J (x.left ≫ Ψ)) (J' x.left)) fun a b d => ?_
    have q : (lift a (lift b d)).left ≫ (cubeMapOf hgp).F3 =
        (lift (pushHom hgp T a) (lift (pushHom hgp T b) (pushHom hgp T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := val_pmaps hc Ht (lift a (lift b d)).left hJ hJ'
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw wL q z (J (q ≫ Ψ)) (J' q))) rfl)
  · obtain ⟨J, hJ⟩ := good y
    have e := val_pmaps hc₂ Hs (eSec G') hJ hJ'
    have e₁ : val s (eSec G' ≫ Ψ) y J = 1 := by
      rw [he]
      exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hs1 f).trans (val_one _))
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    rw [e₁, Fin.prod_univ_two] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul] at e
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact e.symm
end GlobalTheory
