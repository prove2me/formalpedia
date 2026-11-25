-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.exists_nhds_eq_ptOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:32:43.480955+00:00
-- url     : https://prove2.me/submissions/73d9d967-9f05-486b-80b7-3147bc664a81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_exists_specOver_nhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]
omit [W.IsElliptic]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {T : Over (Spec (.of R))} (p q : T ⟶ schemeOver W) (t : T.left) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A) (j : specOver R A ⟶ T) (P Q : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q),
      IsOpenImmersion j.left ∧ t ∈ Set.range j.left ∧ j ≫ p = ptOver W P hP ∧
        j ≫ q = ptOver W Q hQ := by
  have hc : ∀ x : scheme W, ∃ i, x ∈ coordOpen W i := fun x => by
    rcases (coordOpen_one_sup_coordOpen_two W).ge (Set.mem_univ x) with h | h
    exacts [⟨_, h⟩, ⟨_, h⟩]
  obtain ⟨a, ha⟩ := hc (p.left t)
  obtain ⟨b, hb⟩ := hc (q.left t)
  obtain ⟨A, _, _, j, hj, ht, hV⟩ := exists_specOver_nhds T
    (V := p.left ⁻¹ᵁ coordOpen W a ⊓ q.left ⁻¹ᵁ coordOpen W b) ⟨ha, hb⟩
  obtain ⟨P, hP, -, eP⟩ := exists_eq_ptHom_of_preimage_eq_top W (algebraMap R A) (j ≫ p).left
    (Over.w (j ≫ p)) a (top_le_iff.mp fun y hy => (hV.ge hy).left)
  obtain ⟨Q, hQ, -, eQ⟩ := exists_eq_ptHom_of_preimage_eq_top W (algebraMap R A) (j ≫ q).left
    (Over.w (j ≫ q)) b (top_le_iff.mp fun y hy => (hV.ge hy).right)
  exact ⟨A, _, _, j, P, Q, hP, hQ, hj, ht, Over.OverMorphism.ext eP, Over.OverMorphism.ext eQ⟩
end GlobalTheory.WeierstrassCurve
