-- Prove2me | solution 1 for GlobalTheory.AbLaw.PowVanish.exists_iso_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:00.451811+00:00
-- url     : https://prove2.me/submissions/3db3b7a0-c7c0-4fff-8567-6ede23627f4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.PowVanish
namespace GlobalTheory.AbLaw.PowVanish
theorem _root_.solution {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (f : X ⟶ X) (k n r N t : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, f] ![k, -1])) (hα : α.IsGen) (h : k * n = r + N * t) :
    ∃ w : LB.Iso ((pw L n).pull f) ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)), w.IsGen := by
  have l₁ : ∀ (p : PUnit → L.ι × (PUnit → L.ι)) (q : PUnit → L.ι),
      ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)).U p ⊓ ((pw L n).pull f).U q ≤
        LB.wchart L (K := Fin 2) ![𝟙 X, f] ![(p PUnit.unit).1, q PUnit.unit] := fun p q y hy =>
    Set.mem_iInter.2 fun i => by
      fin_cases i
      · exact (mem_pull.1 hy.1).1
      · exact mem_pull.1 hy.2
  have l₂ : ∀ (p : PUnit → L.ι × (PUnit → L.ι)) (q : PUnit → L.ι),
      ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)).U p ⊓ ((pw L n).pull f).U q ≤
        L.U ((p PUnit.unit).2 PUnit.unit) ⊓ L.U (p PUnit.unit).1 := fun p q y hy =>
    ⟨mem_pull (L := L) (F := 𝟙 X).1 (mem_pull.1 hy.1).2, (mem_pull.1 hy.1).1⟩
  refine ⟨⟨fun p => res (l₁ p.1 p.2) (α.s _) ^ n * res (l₂ p.1 p.2) (L.g _ _) ^ (N * t)⟩,
    fun p q => unit_ext fun y hy => ?_⟩
  have val : ∀ (p : PUnit → L.ι × (PUnit → L.ι)) (q : PUnit → L.ι),
      y ∈ ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).pull (𝟙 X)).U p ⊓ ((pw L n).pull f).U q →
      gm (𝟙 X) y _ (res (l₁ p q) (α.s _) ^ n * res (l₂ p q) (L.g _ _) ^ (N * t)) =
        gm (𝟙 X) y (LB.wchart L (K := Fin 2) ![𝟙 X, f] ![(p PUnit.unit).1, q PUnit.unit]) (α.s _) ^ n *
          gm (𝟙 X) y _ (L.g ((p PUnit.unit).2 PUnit.unit) (p PUnit.unit).1) ^ (N * t) := fun p q hp => by
    rw [map_mul, map_zpow, map_zpow]
    exact congrArg₂ (fun a b => a ^ n * b ^ (N * t)) (gm_res _ y (l₁ p q) hp _) (gm_res _ y (l₂ p q) hp _)
  refine ((gm_res (𝟙 X) y _ hy _).trans (val p.1 p.2 hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div _ _ (𝟙 X) y p q hy)
    ((gm_res (𝟙 X) y _ hy _).trans (val q.1 q.2 hy.2)))).trans ?_
  have hp := l₂ _ _ hy.1
  have hq := l₂ _ _ hy.2
  have e₁ := gen_trans hα (𝟙 X) y (l₁ _ _ hy.1) (l₁ _ _ hy.2)
  have e₂ := gm_pull_g (pw L n) f (𝟙 X) y p.2 q.2 hy.1.2 hy.2.2
  have e₃ := gm_pull_g (tw (pw L r) (pw (L.pull (𝟙 X)) N) t) (𝟙 X) (𝟙 X) y p.1 q.1 hy.1.1 hy.2.1
  have e₄ : gm (𝟙 X ≫ 𝟙 X) y _ ((tw (pw L r) (pw (L.pull (𝟙 X)) N) t).g (p.1 PUnit.unit) (q.1 PUnit.unit)) =
      gm (𝟙 X) y _ (L.g (p.1 PUnit.unit).1 (q.1 PUnit.unit).1) ^ r *
        (gm (𝟙 X) y _ (L.g ((p.1 PUnit.unit).2 PUnit.unit) ((q.1 PUnit.unit).2 PUnit.unit)) ^ (N * t)) := by
    rw [Category.comp_id]
    refine (gm_div _ _ (𝟙 X) y (p.1 PUnit.unit) (q.1 PUnit.unit) ⟨mem_pull.1 hy.1.1, mem_pull.1 hy.2.1⟩).trans ?_
    refine congrArg₂ (· * ·) (map_zpow _ _ _) ?_
    have e := gm_pull_g L (𝟙 X) (𝟙 X) y (p.1 PUnit.unit).2 (q.1 PUnit.unit).2 (mem_pull.1 hy.1.1).2
      (mem_pull.1 hy.2.1).2
    rw [Category.comp_id] at e
    rw [← e, zpow_mul, ← inv_inv ((_ ^ N) ^ t), ← zpow_neg]
    exact congrArg (·⁻¹) ((map_zpow _ _ _).trans (congrArg (· ^ (-t)) (map_zpow _ _ _)))
  have e₅ : gm (𝟙 X ≫ f) y _ ((pw L n).g (p.2 PUnit.unit) (q.2 PUnit.unit)) =
      gm (𝟙 X ≫ f) y _ (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)) ^ n := map_zpow _ _ _
  have c₁ := gm_cocycle hL (𝟙 X) y hp.1 hp.2 hq.2
  have c₂ := gm_cocycle hL (𝟙 X) y hp.1 hq.1 hq.2
  have e₆ : trF (L := L) (K := Fin 2) ![𝟙 X, f] ![k, -1] (𝟙 X) y ![(p.1 PUnit.unit).1, p.2 PUnit.unit]
      ![(q.1 PUnit.unit).1, q.2 PUnit.unit] =
      gm (𝟙 X) y _ (L.g (p.1 PUnit.unit).1 (q.1 PUnit.unit).1) ^ k *
        (gm (𝟙 X ≫ f) y _ (L.g (p.2 PUnit.unit) (q.2 PUnit.unit)))⁻¹ := by
    rw [trF, Fin.prod_univ_two, ← zpow_neg_one]
    exact congrArg₂ (· * ·) (congrArg (fun s => gm s y _ _ ^ k) (Category.comp_id (𝟙 X))) rfl
  refine (congrArg₂ (· * ·) (congrArg₂ (fun a b => a * b⁻¹) (e₃.trans e₄) (e₂.trans e₅)) rfl).trans ?_
  refine Eq.trans ?_ (congrArg₂ (fun a b => a ^ n * b) (e₁.trans (congrArg₂ (· * ·) e₆ rfl)) rfl).symm
  have alg : ∀ {U : Type} [CommGroup U] (a b c d e s u : U), d * a = u → b * e = u →
      a ^ r * b ^ (N * t) * (c ^ n)⁻¹ * (s ^ n * e ^ (N * t)) = (a ^ k * c⁻¹ * s) ^ n * d ^ (N * t) := by
    intro U _ a b c d e s u h₁ h₂
    have hd : d = b * e * a⁻¹ := by rw [h₂, ← h₁, mul_inv_cancel_right]
    have hr : r = k * n - N * t := by rw [h]; ring
    subst hd hr
    simp only [mul_zpow, inv_zpow, zpow_sub, ← zpow_mul]
    simp only [_root_.mul_comm, mul_left_comm, _root_.mul_assoc]
  exact alg _ _ _ _ _ _ _ c₁ c₂
end GlobalTheory.AbLaw.PowVanish
