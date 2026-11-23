-- Prove2me | solution 1 for GlobalTheory.AffineQuotient.of_charts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:45.638192+00:00
-- url     : https://prove2.me/submissions/6c43fc18-c57e-4794-aa9d-ed83ccc61926

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoequifiberedDiagramMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P] {ι : Type}
    (X' Y' : ι → Scheme.{0}) (u : ∀ i, X' i ⟶ X) (v : ∀ i, Y' i ⟶ Y) (f' : ∀ i, X' i ⟶ Y' i)
    [∀ i, IsOpenImmersion (v i)] (hv : ∀ y, ∃ i z, v i z = y)
    (h : ∀ i, IsPullback (f' i) (u i) (v i) f) (hP : ∀ i, P (f' i)) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers ι Y' v hv) fun i ↦ ?_
  have := (h i).flip.isoPullback_inv_snd
  change P (pullback.snd f (v i))
  rw [← this, MorphismProperty.cancel_left_of_respectsIso P]
  exact hP i
end GlobalTheory.AffineQuotient
