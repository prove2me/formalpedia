-- Prove2me | solution 1 for GlobalTheory.GlueLineBundle.pgen_isoGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:54:51.30752+00:00
-- url     : https://prove2.me/submissions/deb28d0c-9ede-46ec-924c-d91729948266

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
import Theorems.Thm_GlobalTheory_GlueLineBundle_gm_glue_g
import Theorems.Thm_GlobalTheory_GlueLineBundle_eq_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} {V : A → X.Opens} {M : ∀ a, LB (V a).toScheme}
namespace GlobalTheory.GlueLineBundle
theorem _root_.solution (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hM : ∀ a, (M a).IsLB) (a : A) :
    PGen (isoGen (V := V) (M := M) a) := by
  intro Y f y j j' k k' hj hj' hk hk'
  obtain ⟨b, i⟩ := j
  obtain ⟨b', i'⟩ := j'
  have hb : a = b := eq_of_mem hdisj (f y) hj
  have hb' : a = b' := eq_of_mem hdisj (f y) hj'
  subst hb hb'
  have hi : f y ∈ (M a).U i := (V a).ι.apply_mem_image_iff.1 hj
  have hi' : f y ∈ (M a).U i' := (V a).ι.apply_mem_image_iff.1 hj'
  have e1 : gw (isoGen a) f y ⟨a, i⟩ k = gm f y _ ((M a).g i k) :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i⟩) k) Y f y i rfl hi hk
  have e2 : gw (isoGen a) f y ⟨a, i'⟩ k' = gm f y _ ((M a).g i' k') :=
    Classical.choose_spec (exists_isoUnit (V := V) (M := M) a (fun _ => ⟨a, i'⟩) k') Y f y i' rfl hi' hk'
  rw [e1, e2, gm_glue_g V M a f y i i' hi hi', mul_right_comm, gm_cocycle (hM a) f y hi hi' hk',
    ← gm_cocycle (hM a) f y hi hk hk', mul_inv_cancel_right]
end GlobalTheory.GlueLineBundle
