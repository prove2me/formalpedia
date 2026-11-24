-- Prove2me | solution 1 for GlobalTheory.ToSplit.exists_gtDatum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:01:47.374637+00:00
-- url     : https://prove2.me/submissions/6d808a2f-b181-42e4-8959-2fe5480f6886

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_ToSplit_gm_res_pre
import Theorems.Thm_P2M_GlobalTheory_ToSplit_gm_id_pull__a5960ce669d6
import Theorems.Thm_GlobalTheory_ToSplit_charGerm_eq
import Theorems.Thm_GlobalTheory_ToSplit_act_apply
import Theorems.Thm_GlobalTheory_ToSplit_monoidHom_ext_basis
import Theorems.Thm_GlobalTheory_ToSplit_isAffineHom_left
import Theorems.Thm_GlobalTheory_ToSplit_IsFrame_trans_id
import Theorems.Thm_GlobalTheory_isAffineOpen_and_bijective_of_weight_units
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] SplitExt.free SplitExt.finite
variable {S : Scheme.{0}} (E : SplitExt S) {G : Over S} [GrpObj G]
  {q : G ⟶ E.B} {i : splitTorus S E.X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[E.B]))
include hk
namespace GlobalTheory.ToSplit
theorem _root_.solution (u : ∀ χ j, Γ(G.left, q.left ⁻¹ᵁ (E.O χ).L.U j)ˣ)
    (hu : ∀ χ, IsFrame q i χ (E.O χ) (u χ)) : ∃ d : E.GtDatum G, d.q = q ∧ d.i = i := by
  let v : ∀ (j : E.ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ := fun j k =>
    res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (u (E.basis k) (j k))
  have hv : ∀ j k (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j →
      gm r z _ (v j k) = gm r z _ (u (E.basis k) (j k)) := fun j k Z r z hz =>
    gm_res_pre _ _ _ _ hz _
  refine ⟨{
    q := q
    i := i
    q_hom := ‹_›
    i_hom := ‹_›
    q_flat := ‹_›
    q_surjective := ‹_›
    q_affine := isAffineHom_left hk
    isKernel := hk
    u := v
    coord := fun j V hV h => ?_
    trans := fun j j' k => unit_ext fun y hy => ?_
    act_le := fun j y hy => ?_
    equiv := fun j k => unit_ext fun y hy => ?_
    unit_norm := fun j k => unit_ext fun y hy => ?_ }, rfl, rfl⟩
  · refine (isAffineOpen_and_bijective_of_weight_units S E.X G E.B q i ‹_› ‹_› ‹_› ‹_› ‹_› hk V hV
      _ fun χ => HasWeight.appLE ?_).2
    intro Z t g z hz
    have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rwa [act_apply hk]
    let w : Multiplicative E.X →* Γ(G.left, q.left ⁻¹ᵁ V)ˣ := AddMonoidHom.toMultiplicativeLeft
      (E.basis.constr ℤ (fun k => Additive.ofMul
        (res (Scheme.Hom.preimage_mono q.left h) (v j k)))).toAddMonoidHom
    have hw : ∀ k, w (Multiplicative.ofAdd (E.basis k)) =
        res (Scheme.Hom.preimage_mono q.left h) (v j k) := fun k =>
      congrArg Additive.toMul (E.basis.constr_basis ℤ (fun k => Additive.ofMul
        (res (Scheme.Hom.preimage_mono q.left h) (v j k))) k)
    have : (gm ((t ≫ i) * g).left z _).comp w = charGerm z t * (gm g.left z _).comp w :=
      monoidHom_ext_basis E.basis fun k => by
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, hw,
          gm_res_pre _ _ _ _ hz', gm_res_pre _ _ _ _ hz, hv _ _ _ _ _ (h hz'), hv _ _ _ _ _ (h hz)]
        exact (hu _).1 _ Z t g z (E.chart_le j k (h hz))
    exact DFunLike.congr_fun this (Multiplicative.ofAdd χ)
  · have hy' : q.left y ∈ E.chart j ⊓ E.chart j' := hy
    refine ((gm_res (𝟙 _) y _ hy _).trans (hv j' k _ (𝟙 _) y hy.2)).trans (Eq.trans ?_
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_id_pull' _ _ hy' _).trans
        ((gm_res _ _ _ hy' _).trans
          ((hu _).trans_id _ _ y (E.chart_le j k hy.1) (E.chart_le j' k hy.2))))
        ((gm_res (𝟙 _) y _ hy _).trans (hv j k _ (𝟙 _) y hy.1)))).symm)
    exact (div_mul_cancel _ _).symm
  · change q.left (((fst _ G ≫ i) * snd _ G).left y) ∈ E.chart j
    rw [act_apply hk]
    exact hy
  · have hy' : q.left (((fst _ G ≫ i) * snd _ G).left y) ∈ E.chart j := by
      rw [act_apply hk]
      exact hy
    refine ((gm_id_res_pull _ y _ hy _).trans (hv j k _ _ y hy')).trans (Eq.trans ?_
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_id_res_pull _ y _ hy _).trans
        (charGerm_eq y (fst _ G) (E.basis k)).symm)
        ((gm_id_pull' _ y hy _).trans (hv j k _ _ y hy)))).symm)
    exact (hu _).1 _ _ _ _ y (E.chart_le j k hy)
  · refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) ((gm_id_res_pull _ y _ hy _).trans
      (hv j k _ _ y hy.1)) ((gm_res (𝟙 _) y _ hy _).trans
        ((hu _).2.2 (j k) y (mem_pull.1 hy.2)))).trans ?_)
    rw [map_one, mul_inv_cancel]
end GlobalTheory.ToSplit
