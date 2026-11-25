-- Prove2me | solution 1 for GlobalTheory.IdCompMul.mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:01:53.177055+00:00
-- url     : https://prove2.me/submissions/90e61244-c489-4208-9aab-2695824f0aad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionComponentsPreimageOfIsPullbackStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulMemIdentityComponentOfRationalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityComponentsSmoothGroupSchemeMulMem
import Theorems.Thm_GlobalTheory_IdCompMul_mul_mem_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
noncomputable section
open GlobalTheory GlobalTheory.IdCompMul
namespace GlobalTheory.IdCompMul
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ w : (G ⊗ G).left, (fst G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (snd G G).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} → (μ[G]).left w ∈ {x : G.left | x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))} := by
  intro S G instG hG w h1 h2
  let κ := (G ⊗ G).left.residueField w
  let j : Spec (CommRingCat.of κ) ⟶ (G ⊗ G).left := (G ⊗ G).left.fromSpecResidueField w
  let p : Spec (CommRingCat.of κ) ⟶ S := j ≫ (G ⊗ G).hom
  let a : Over.mk p ⟶ G := Over.homMk (j ≫ (fst G G).left) (by simp [p])
  let b : Over.mk p ⟶ G := Over.homMk (j ≫ (snd G G).left) (by simp [p, pullback.condition])
  have hw : j (IsLocalRing.closedPoint κ) = w := Scheme.fromSpecResidueField_apply w _
  have hl : lift a b = (Over.homMk j rfl : Over.mk p ⟶ G ⊗ G) := by
    apply CartesianMonoidalCategory.hom_ext
    · ext1
      simp [a]
    · ext1
      simp [b]
  have hm := mul_mem_of_field G hG κ p a b
    (by
      convert h1 using 2
      exact congrArg (fst G G).left hw)
    (by
      convert h2 using 2
      exact congrArg (snd G G).left hw)
  rw [Hom.mul_def, Over.comp_left, hl] at hm
  convert hm using 2
  exact (congrArg (μ[G]).left hw).symm
end GlobalTheory.IdCompMul
