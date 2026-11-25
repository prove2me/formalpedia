-- Prove2me | solution 1 for GlobalTheory.KernelEigen.commIsOf_of_weilIs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:56.077678+00:00
-- url     : https://prove2.me/submissions/e162448a-3e05-4bf7-a820-b791236a619e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TranslatePullbackEigensection
import Theorems.Thm_GlobalTheory_CommPairing_commIsOf_iff
import Theorems.Thm_GlobalTheory_CommPairing_exists_pull
import Theorems.Thm_GlobalTheory_CommPairing_whisker_translT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.KernelEigen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}
namespace GlobalTheory.KernelEigen
theorem _root_.solution (hL : L.IsLB) [Unique T.left] {n : ℤ} (θx θy : ThetaGrp A L n T)
    {e : Γ(T.left, ⊤)ˣ} (H : WeilIs A L n θx.pt θy.pt e) : CommIsOf A L n θx θy e := by
  obtain ⟨V, hV, -, H⟩ := H default
  obtain rfl : V = ⊤ := top_le_iff.1 fun x _ => by rw [Subsingleton.elim x default]; exact hV
  let h := overResι (T := T) ⊤
  have : IsIso h.left := inferInstanceAs (IsIso (Scheme.topIso T.left).hom)
  have : IsIso ((Over.forget S).map h) := this
  have : IsIso h := isIso_of_reflects_iso h (Over.forget S)
  obtain ⟨θx', hx, vx⟩ := exists_pull hL h θx
  obtain ⟨θy', hy, vy⟩ := exists_pull hL h θy
  have H' := (commIsOf_iff hL _ _ _).1 (H θx' θy' hx hy)
  rw [commIsOf_iff hL]
  intro Z r z J hJ
  obtain ⟨r', rfl⟩ : ∃ r' : Z ⟶ (overRes (T := T) ⊤ ⊗ A).left, r = r' ≫ (h ▷ A).left :=
    ⟨r ≫ (inv (h ▷ A)).left, by rw [Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left,
      Category.comp_id]⟩
  have t : ∀ x : T ⟶ A, (r' ≫ (translT A (h ≫ x)).left) ≫ (h ▷ A).left =
      (r' ≫ (h ▷ A).left) ≫ (translT A x).left := fun x => by
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whisker_translT]
  have g : gm (r' ≫ (fst (overRes (T := T) ⊤) A).left) z ⊤ (Units.map h.left.appTop.hom.toMonoidHom e) =
      gm ((r' ≫ (h ▷ A).left) ≫ (fst T A).left) z ⊤ e := by
    refine (gm_pull (r' ≫ (fst (overRes (T := T) ⊤) A).left) h.left z ⊤ trivial e).trans ?_
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, whiskerRight_fst]
  have := H' Z r' z J hJ
  rw [vx _ _ z J hJ, vx _ _ z J hJ, vy _ _ z J hJ, vy _ _ z J hJ, hx, hy, t, t] at this
  exact this.trans (congrArg _ g)
end GlobalTheory.KernelEigen
