-- Prove2me | solution 1 for GlobalTheory.UU.TQ.Desc.cubV_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:50.910898+00:00
-- url     : https://prove2.me/submissions/b0d29b93-adac-49e8-9820-f3e159973e45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_NotExistsEvenTwistSymOne
import Theorems.Thm_GlobalTheory_UU_TQ_comp_i_q
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isCub_cubV


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UU
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {X : Type} [AddCommGroup X]
namespace GlobalTheory.UU
namespace TQ.Desc
theorem _root_.solution {Q : TQ G X} {P : CP G} (D : Q.Desc P) {T : Over S} {z : T.left} {J}
    (hJ : Good D.M.L.L z J) (h : Q.q.left ≫ Q.B.hom = G.hom ≫ 𝟙 S) (x : T ⟶ splitTorus S X) (y u : T ⟶ G) :
    @id (T.left.presheaf.stalk z)ˣ (cubV D.M.c (T := Over.mk (T.hom ≫ 𝟙 S)) z J
      (toBase h (x ≫ Q.i)) (toBase h y) (toBase h u)) = 1 := by
  have e : toBase h (x ≫ Q.i) = 1 := by
    ext
    have h1 := congrArg (fun f => f.left) (TQ.comp_i_q Q x)
    simp only [Over.comp_left] at h1
    rw [one_left] at h1 ⊢
    simp [toBase, h1]
  rw [e]
  exact (isCub_cubV D.M.c hJ).face _ _
end TQ.Desc
end GlobalTheory.UU
