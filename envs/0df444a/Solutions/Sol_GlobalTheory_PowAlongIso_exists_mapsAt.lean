-- Prove2me | solution 1 for GlobalTheory.PowAlongIso.exists_mapsAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:28:01.825969+00:00
-- url     : https://prove2.me/submissions/9cd1bc02-9b7d-4b65-917b-bc43e3d237c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
import Theorems.Thm_GlobalTheory_PowAlongIso_mem_wchart_comp
import Theorems.Thm_GlobalTheory_PowAlongIso_mapsAt_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
open GlobalTheory GlobalTheory.PowAlongIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)
variable {X X' X'' Y Y' Y₀ Z : Scheme.{0}}
variable {M : LB X} {M' : LB X'} {M'' : LB X''} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
namespace GlobalTheory.PowAlongIso
theorem _root_.solution (hM' : M'.IsLB) {E : X'' ⟶ X'} {pr' : Fin j → (X'' ⟶ X)} (hpr : ∀ i, pr' i = E ≫ pr i)
    {w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))} {w' : LB.Iso M'' (M'.pull E)}
    {w'' : LB.Iso M'' (LB.LinComb M pr' (fun _ => 1))}
    (T : ∀ (Z : Scheme.{0}) (f : Z ⟶ X'') (z : Z)
      (a : Fin j → M.ι) (b : M'.ι) (c : M''.ι), f z ∈ LB.wchart M pr' a → E (f z) ∈ M'.U b → f z ∈ M''.U c →
      bw w'' f z a c = bw w (f ≫ E) z a b * gw w' f z b c)
    {p : Y ⟶ X'} {p' : Y ⟶ X''} (hp : p' ≫ E = p) {a : LB.Gen (M'.pull p)} {a' : LB.Gen (M''.pull p')}
    (H : PMaps w' (K := PUnit) (fun _ => p') (fun _ => p) (fun _ => 1) a' a (𝟙 _))
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (c : LB.Gen (LB.LinComb M φ ε))
    (h : ∃ b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p ≫ pr i) (fun _ => 1)),
      GeneratorPullback.MapsAt M M' pr w p 1 a b ∧ LB.Gen.Corr M _ _ _ _ b c) :
    ∃ b : LB.Gen (LB.LinComb M (K := Fin j) (fun i => p' ≫ pr' i) (fun _ => 1)),
      GeneratorPullback.MapsAt M M'' pr' w'' p' 1 a' b ∧ LB.Gen.Corr M _ _ _ _ b c := by
  obtain rfl : pr' = fun i => E ≫ pr i := funext hpr
  subst hp
  obtain ⟨b, hb, hc⟩ := h
  have tr : ∀ ψ : Fin j → (Y ⟶ X), (fun i => (p' ≫ E) ≫ pr i) = ψ →
      ∃ b' : LB.Gen (LB.LinComb M ψ (fun _ => 1)), LB.Gen.Corr M _ _ _ _ b' c ∧ ∀ y jN,
        gm (𝟙 Y) y (LB.wchart M ψ jN) (b'.s jN) =
          gm (𝟙 Y) y (LB.wchart M (fun i => (p' ≫ E) ≫ pr i) jN) (b.s jN) := by
    rintro _ rfl
    exact ⟨b, hc, fun _ _ => rfl⟩
  obtain ⟨b', hc', hb'⟩ := tr (fun i => p' ≫ E ≫ pr i) (funext fun i => Category.assoc _ _ _)
  refine ⟨b', (mapsAt_iff _ _ _ _ _).2 fun y jN jL h₁ h₂ => ?_, hc'⟩
  obtain ⟨k, hk⟩ := exists_chart hM' (E (p' y))
  have e := H Y (𝟙 Y) y (fun _ => k) (fun _ => jL) (fun _ => hk) (fun _ => h₂)
  rw [Fintype.prod_unique, Category.id_comp, Category.id_comp] at e
  rw [hb', (mapsAt_iff _ _ _ _ _).1 hb y jN k ((mem_wchart_comp (E := E)).1 h₁) hk, T Y p' y jN k jL h₁ hk h₂, mul_zpow,
    _root_.mul_assoc]
  exact congrArg _ e
end GlobalTheory.PowAlongIso
