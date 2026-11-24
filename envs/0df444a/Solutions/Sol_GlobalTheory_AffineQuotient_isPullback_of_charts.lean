-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.isPullback_of_charts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:56:37.429007+00:00
-- url     : https://prove2.me/submissions/80490c3c-47f8-4325-8f95-5b37f778192c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap
import Theorems.Thm_P2M_GlobalTheory_AffineQuotient___toQuot_f55bcab7a372
import Theorems.Thm_P2M_GlobalTheory_AffineQuotient___fromQuot_2934bbd4beb2
import Theorems.Thm_GlobalTheory_AffineQuotient_toQuot_fromQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.AffineQuotient.ι_toQuot
attribute [reassoc] GlobalTheory.AffineQuotient.ι_fromQuot
attribute [reassoc (attr := simp)] GlobalTheory.AffineQuotient.toQuot_fromQuot

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineQuotient
open Scheme.AffineZariskiSite
variable {W X Y : Scheme.{0}}
variable (f : X ⟶ Y) (g : W ⟶ Y) (a : W ⟶ X) (ha : a ≫ f = g) (p : W ⟶ X) (hp : p ≫ f = g)
variable [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
set_option backward.isDefEq.respectTransparency false
omit [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
namespace GlobalTheory.AffineQuotient
theorem _root_.solution {Z Q : Scheme.{0}} (b : W ⟶ Z) (q : X ⟶ Q) (q' : Z ⟶ Q) {ι : Type}
    (W' X' : ι → Scheme.{0}) (u : ∀ i, W' i ⟶ W) (v : ∀ i, X' i ⟶ X) (a' : ∀ i, W' i ⟶ X' i)
    [∀ i, IsOpenImmersion (v i)] (hv : ∀ y, ∃ i z, v i z = y)
    (h : ∀ i, IsPullback (a' i) (u i) (v i) a)
    (h' : ∀ i, IsPullback (a' i) (u i ≫ b) (v i ≫ q) q') : IsPullback a b q q' := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (Scheme.Cover.mkOfCovers ι X' v hv) fun i ↦ ?_
  change IsPullback (pullback.snd a (v i)) (pullback.fst a (v i) ≫ b) (v i ≫ q) q'
  refine (h' i).of_iso (h i).flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    <;> simp
end GlobalTheory.AffineQuotient
