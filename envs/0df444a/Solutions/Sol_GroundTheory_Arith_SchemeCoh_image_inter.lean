-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.image_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:13.391566+00:00
-- url     : https://prove2.me/submissions/cff0c396-9a32-419d-b937-84b1821911f3

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] {κ : Type w}
    (U : κ → Y.Opens) {n : ℕ} (i : Fin (n + 1) → κ) :
    g ''ᵁ inter (X := Y.toTopCat) U i = inter (X := X.toTopCat) (fun a => g ''ᵁ U a) i := by
  have key : ∀ (W : Y.Opens) (x : X), x ∈ g ''ᵁ W ↔ ∃ y ∈ W, g y = x := fun W x => by
    rw [← SetLike.mem_coe, Scheme.Hom.coe_image]
    rfl
  refine SetLike.ext fun x => ?_
  rw [mem_inter_iff, key]
  constructor
  · rintro ⟨y, hy, rfl⟩ a
    exact (key _ _).2 ⟨y, (mem_inter_iff U i y).1 hy a, rfl⟩
  · intro hx
    choose y hy hyx using fun a => (key _ x).1 (hx a)
    refine ⟨y 0, (mem_inter_iff U i (y 0)).2 fun a => ?_, hyx 0⟩
    have : y a = y 0 := g.isOpenEmbedding.injective ((hyx a).trans (hyx 0).symm)
    rw [← this]
    exact hy a
end GroundTheory.Arith.SchemeCoh
