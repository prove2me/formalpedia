-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.acyc_of_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:39.498946+00:00
-- url     : https://prove2.me/submissions/0e5e32fa-e5a6-45e5-8ad8-a00b8a1b6a16

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_rm_rm
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_rm_id
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_d
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_pt
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_map

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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (hCx : CxSt) (hHt : HtpySt) (hA : AffAcycSt) [Quiver.IsThin E] (f : E ⥤ AffOp X)
    (W : X.affineOpens) (hle) (t : E) (ht : W.1 ≤ (f.obj t).unop.1) (e : E ⥤ E)
    (a₁ : ∀ T, T ⟶ e.obj T) (a₂ : ∀ T, t ⟶ e.obj T)
    (he : ∀ T, (f.obj T).unop.1 ≤ (f.obj (e.obj T)).unop.1) : Acyc s f W.1 hle := by
  let c₁ := (Functor.const ((Fin 1)ᵒᵖ)).obj t
  let c₂ := (Functor.const E).obj (op (0 : Fin 1))
  have hc₁ : ∀ T, ((pt W).obj T).unop.1 ≤ (f.obj (c₁.obj T)).unop.1 := fun _ ↦ ht
  have hc₂ : ∀ T, (f.obj T).unop.1 ≤ ((pt W).obj (c₂.obj T)).unop.1 := hle
  have hcc : ∀ T, (f.obj T).unop.1 ≤ (f.obj ((c₂ ⋙ c₁).obj T)).unop.1 := fun T ↦ (hle T).trans ht
  let m₀ := rm s f f (𝟭 E) (fun _ ↦ le_rfl)
  let mₑ := rm s f f e he
  let mc := rm s f f (c₂ ⋙ c₁) hcc
  have H₁ := hHt R E (f ⋙ OAff s) E (f ⋙ OAff s) m₀ mₑ
    { app := a₁, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
    (fun T b ↦ (Sec.res_res s _ _ b).symm.trans rfl)
  have H₂ := hHt R E (f ⋙ OAff s) E (f ⋙ OAff s) mc mₑ
    { app := a₂, naturality := fun _ _ _ ↦ Subsingleton.elim _ _ }
    (fun T b ↦ (Sec.res_res s _ _ b).symm.trans rfl)
  have hp : ∀ i z, pulln (rm s (pt W) f c₂ hc₂) i (pulln (rm s f (pt W) c₁ hc₁) i z) = pulln mc i z :=
    fun i z ↦ pull_rm_rm s f (pt W) f c₁ c₂ hc₁ hc₂ hcc i z
  have h₀ : ∀ i z, pulln m₀ i z = z := fun i z ↦ pull_rm_id s f _ i z
  refine acyc_of_map s hCx hA f (pt W) c₁ hc₁ W hle (fun _ ↦ le_rfl) (fun x hx hx' ↦ ?_)
    (fun n x hx ⟨y, hy⟩ ↦ ?_) (acyc_pt s hA W)
  · have k₁ := (H₁.1 x hx).trans (H₂.1 x hx).symm
    rw [h₀, ← hp, hx', map_zero] at k₁
    exact k₁
  · obtain ⟨y₁, e₁⟩ := H₁.2 n x hx
    obtain ⟨y₂, e₂⟩ := H₂.2 n x hx
    refine ⟨pulln (rm s (pt W) f c₂ hc₂) n y + y₁ - y₂, ?_⟩
    rw [map_sub, map_add, ← e₁, ← e₂, ← pull_d hCx, hy, hp, h₀]
    abel
end GlobalTheory.CompanionTheory.Descent
