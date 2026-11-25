-- Prove2me | solution 1 for GlobalTheory.LieExt.lieMult_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:26:30.083351+00:00
-- url     : https://prove2.me/submissions/06272f62-858d-444e-84a0-f2c812af7f50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LieMultIffFinrank
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_list_prod_tan__79ee0da3542e
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_mem_eigLat_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_eq_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_v
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_exists_w
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_pre
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_rel_prod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_scale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tcoord_spec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_eig_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_tvec_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.LieExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)
  {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)
include hc hg hab hact'
namespace GlobalTheory.LieExt
theorem _root_.solution {N : ℕ} (hN : Module.finrank k (eigLat hx act' (fun a => τ a)) = N) :
    Geo.Tor.LieMult act tk τ N := by
  let B := Module.finBasisOfFinrankEq k _ hN
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔
      ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  choose vB hv using fun i => rel_exists_w hc hg (tvec (x := x) (B i : Fin n → k))
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k)).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv i)
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • (B i : Fin n → k)) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan' hx (fun i => spMap (scaleD (d i)) ≫ tvec (x := x) (B i : Fin n → k))
      (fun i => isTan_scale (d i) (isTan_tvec hx _))
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      (tcoord_scale hx (d i) (isTan_tvec hx _)).trans (by rw [tcoord_tvec])
  refine ⟨vB, fun i => (hT _ _ (hv i)).2 ⟨isTan_tvec hx _, (hmem _).1 (B i).2⟩, fun w hw => ?_⟩
  obtain ⟨v, hwv⟩ := rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) w
  obtain ⟨ht, he⟩ := (hT _ _ hwv).1 hw
  obtain ⟨c, rfl⟩ : ∃ c, tvec (x := x) c = v := ⟨_, (tcoord_spec hx v ht).symm⟩
  let c' : eigLat hx act' (fun a => τ a) := ⟨c, (hmem c).2 he⟩
  have key : ∀ d : Fin N → k, (∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ w = (List.ofFn u).prod) ↔
      B.equivFun c' = d := fun d => by
    have e₁ : B.equivFun c' = d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
      simp [c']
    have e₂ : w = Wd d ↔ c = ∑ i, d i • (B i : Fin n → k) := by
      refine (rel_eq_iff hc hwv (hPW d)).trans ?_
      rw [hPeq]
      exact ⟨fun h => tvec_inj hx h, fun h => by rw [← h]⟩
    rw [e₁, ← e₂]
    constructor
    · rintro ⟨u, hu, hwu⟩
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      rw [hwu, hu']
    · intro h
      exact ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, h⟩
  exact (existsUnique_congr key).2 existsUnique_eq'
end GlobalTheory.LieExt
