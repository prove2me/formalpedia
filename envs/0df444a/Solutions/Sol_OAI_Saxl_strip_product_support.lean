-- Prove2me | solution 1 for OAI.Saxl.strip_product_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:01:18.735969+00:00
-- url     : https://prove2.me/submissions/2843b18d-1b06-4a36-a6d1-fb09125d0dfd

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StripSupport.lean:L76-L129
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.strip_product_support. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension
import Definitions.Def_OAI_RepresentationTheory_Saxl_SizedStrips
import Theorems.Thm_OAI_Saxl_bandGlue_sector_exists
import Theorems.Thm_OAI_Saxl_bandOrbitMap_equivariant
import Theorems.Thm_OAI_Saxl_bandOrbitMap_nonzero
import Theorems.Thm_OAI_Saxl_placed_strip_restriction
import Theorems.Thm_OAI_Saxl_sector_support_transfer

-- ---- from OAI.RepresentationTheory.Saxl.StripSupport ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Place the smaller tableau on any chosen block, with the remaining strip
colors on its complement. No transitivity or induction rule is assumed. -/
end Saxl

namespace Saxl

/- Required support transfer from a genuine iterated horizontal-strip
restriction and genuine independent high/band cyclic factors. -/
theorem strip_product_support {n a b d : ℕ} {ν μ : YoungDiagram} {bs : List ℕ}
    (hs : SizedStripChain bs ν μ) (s : Tableau a ν) (t : Tableau n μ)
    (e : Fin n ≃ Fin a ⊕ Fin b) (v : WordSpace a d) (u : WordSpace b d)
    (A : Fin d → Prop) (hv : v ∈ alphabetSub a d A)
    (hu : u ∈ alphabetSub b d (fun z => ¬A z))
    (f : Representation.IntertwiningMap (spechtRep s) (cyclic (wordRep a d) v).toRepresentation)
    (hf : f ≠ 0)
    (hband : ∀ (η : YoungDiagram) (r : Tableau b η), η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r) (cyclic (wordRep b d) u).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (positionProduct e v u)).toRepresentation, F ≠ 0 := by
  classical
  obtain ⟨c,F,hF,hFe⟩ := placed_strip_restriction hs s t e
  let G := (subrepInclusion (cyclic (wordRep a d) v)).comp f
  let F₀ : Specht t →ₗ[ℂ] WordSpace a d := G.toLinearMap.comp F
  have hF₀ : F₀ ≠ 0 := by
    intro hz
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    apply Subtype.ext
    exact LinearMap.congr_fun hz x
  have hFb (q : Equiv.Perm (Fin b)) (hq : c ∘ q = c) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e 1 q) x) = F₀ x := by
    change G (F (spechtRep t (sumPerm e 1 q) x)) = G (F x)
    rw [hFe 1 q hq, map_one]
    rfl
  have hFa (h : Equiv.Perm (Fin a)) (x : Specht t) :
      F₀ (spechtRep t (sumPerm e h 1) x) = wordRep a d h (F₀ x) := by
    change G (F (spechtRep t (sumPerm e h 1) x)) = wordRep a d h (G (F x))
    rw [hFe h 1 rfl]
    exact LinearMap.congr_fun (G.isIntertwining' h) (F x)
  let T := bandOrbitMap e (spechtRep t) c F₀
  have hTm (x : Specht t) (w : Fin b → Fin bs.length) : T x w ∈ cyclic (wordRep a d) v := by
    change (∑ g : Equiv.Perm (Fin b), _) ∈ (cyclic (wordRep a d) v).toSubmodule
    apply Submodule.sum_mem
    intro g hg
    apply Submodule.smul_mem
    exact (f (F (spechtRep t (sumPerm e 1 g⁻¹) x))).property
  obtain ⟨L,hL,hLe,hLm,hLs⟩ := bandGlue_sector_exists e (spechtRep t) v u A hv hu hband T
    (bandOrbitMap_nonzero e (spechtRep t) c F₀ hF₀ hFb)
    (bandOrbitMap_equivariant e (spechtRep t) (wordRep a d) c F₀ hFa) hTm
  apply sector_support_transfer (spechtRep t) (fun i => (e i).isLeft = true) A
    (positionProduct e v u) L hL _ hLm
  · intro x w hw
    by_contra hn
    exact hw (hLs x w hn)
  · intro g hg x
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g,hg⟩
    have heq : sumPerm e (leftRestriction e g') (rightRestriction e g') = g := sumPerm_restrictions e g'
    rw [← heq]
    exact hLe _ _ x

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.strip_product_support := @_root_.OAI.Saxl.strip_product_support
