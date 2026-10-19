-- Prove2me | solution 1 for OAI.Saxl.product_mem_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:34:16.461599+00:00
-- url     : https://prove2.me/submissions/78ca8004-ce0e-41e8-81fb-1a043659e630

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/PositionTensor.lean:L80-L124
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.product_mem_cyclic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor

-- ---- from OAI.RepresentationTheory.Saxl.PositionTensor ----
-- TensorProduct.inductionOn (the Lean 4.34 two-case eliminator) is already backported in the imported
-- module OAI.RepresentationTheory.Saxl.StaircaseTensor.

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Concatenation of words on independent position blocks. -/
lemma positionProduct_equivariant {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b))
    (x : WordSpace a d) (y : WordSpace b d) :
    wordRep n d (sumPerm e g h) (positionProduct e x y) =
      positionProduct e (wordRep a d g x) (wordRep b d h y) := by
  funext w
  change x (leftWord e (w ∘ sumPerm e g h)) * y (rightWord e (w ∘ sumPerm e g h)) = _
  have hl : leftWord e (w ∘ sumPerm e g h) = leftWord e w ∘ g := by
    funext i
    simp [leftWord]
  have hr : rightWord e (w ∘ sumPerm e g h) = rightWord e w ∘ h := by
    funext i
    simp [rightWord]
  rw [hl,hr]
  rfl

lemma product_mem_cyclic {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (v : WordSpace a d) (u : WordSpace b d)
    (x : WordSpace a d) (y : WordSpace b d)
    (hx : x ∈ cyclic (wordRep a d) v) (hy : y ∈ cyclic (wordRep b d) u) :
    positionProduct e x y ∈ cyclic (wordRep n d) (positionProduct e v u) := by
  let S := cyclic (wordRep n d) (positionProduct e v u)
  change x ∈ Submodule.span ℂ _ at hx
  change y ∈ Submodule.span ℂ _ at hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h,rfl⟩ := hy
      rw [← positionProduct_equivariant]
      exact S.apply_mem_toSubmodule (sumPerm e g h) (mem_cyclic _ _)
    | zero =>
      have hz : positionProduct e (wordRep a d g v) 0 = 0 := by ext; simp [positionProduct]
      rw [hz]
      exact S.toSubmodule.zero_mem
    | add y z hy hz ihy ihz =>
      have he : positionProduct e (wordRep a d g v) (y+z) =
          positionProduct e (wordRep a d g v) y + positionProduct e (wordRep a d g v) z := by
        ext; simp [positionProduct,mul_add]
      rw [he]
      exact S.toSubmodule.add_mem ihy ihz
    | smul c y hy ih =>
      have he : positionProduct e (wordRep a d g v) (c • y) =
          c • positionProduct e (wordRep a d g v) y := by ext; simp [positionProduct,mul_left_comm]
      rw [he]
      exact S.toSubmodule.smul_mem c ih
  | zero =>
    have hz : positionProduct e 0 y = 0 := by ext; simp [positionProduct]
    rw [hz]
    exact S.toSubmodule.zero_mem
  | add x z hx hz ihx ihz =>
    have he : positionProduct e (x+z) y = positionProduct e x y + positionProduct e z y := by
      ext; simp [positionProduct,add_mul]
    rw [he]
    exact S.toSubmodule.add_mem ihx ihz
  | smul c x hx ih =>
    have he : positionProduct e (c • x) y = c • positionProduct e x y := by
      ext; simp [positionProduct,mul_assoc]
    rw [he]
    exact S.toSubmodule.smul_mem c ih

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.product_mem_cyclic := @_root_.OAI.Saxl.product_mem_cyclic
