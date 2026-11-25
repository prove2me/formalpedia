-- Prove2me | solution 1 for GlobalTheory.HeckeFrCompare.lie_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:11.712584+00:00
-- url     : https://prove2.me/submissions/3f1067b3-8d28-46b2-bb94-714772f04ae8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeFr
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_FibrePushforward
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HkRelFrOfTransportIff
import Theorems.Thm_GlobalTheory_HeckeFrCompare_conj_apply
import Theorems.Thm_GlobalTheory_HeckeFrCompare_eps_cancel
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HeckeFrCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace GlobalTheory.HeckeFrCompare
theorem _root_.solution {Ω : Type} [Field Ω] {p : ℕ} (hp : (p : Ω) ≠ 0) {x x' : Sp Ω ⟶ Xo.X}
    (ψ : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x')
    (v w : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left) :
    (IsTanAt x v ∧ IsTanAt x' w ∧ IsLieImageH p ψ v w) ↔ IsLieImg p (conj x x' ψ) v w := by
  refine and_congr_right fun hv => and_congr_right fun _ => ?_
  have hpush : ∀ a : tEps x ⟶ Xo.univ.t.G, push (conj x x' ψ) (spMap (algebraMap Ω (DualNumber Ω))) a =
      (toFib x _ a ≫ (swap x).hom) ≫ ψ ≫ pullback.fst _ _ := fun a => by
    simp only [push, conj_apply, Category.assoc, swap_inv_snd]
  constructor
  · rintro ⟨u, h₁, h₂, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a : tEps x ⟶ Xo.univ.t.G, a.left = v := ⟨Over.homMk v hv.1, rfl⟩
    refine ⟨a, ha, ?_⟩
    have : toFib x _ a ≫ (swap x).hom = u := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, swap_hom_fst, toFib_snd, h₁, ha]
      · rw [Category.assoc, swap_hom_snd, toFib_fst, h₂]
    rw [hpush, this, ← Category.assoc, eps_cancel (mul_inv_cancel₀ hp), Category.id_comp]
  · rintro ⟨a, rfl, h⟩
    refine ⟨toFib x _ a ≫ (swap x).hom, ?_, ?_, ?_⟩
    · rw [Category.assoc, swap_hom_fst, toFib_snd]
    · rw [Category.assoc, swap_hom_snd, toFib_fst]
    · rw [← hpush, ← h, ← Category.assoc, eps_cancel (inv_mul_cancel₀ hp), Category.id_comp]
end GlobalTheory.HeckeFrCompare
