-- Prove2me | solution 1 for OAI.CanonicalFace198.image_minFace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:51:42.761977+00:00
-- url     : https://prove2.me/submissions/49ca9539-e44a-4277-96e2-b8077ddf91e0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TriangleFace/Faces.lean:L52-L66
-- (upload_full_project.md Phase 4): solution for node OAI.CanonicalFace198.image_minFace. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_TriangleExpansion

-- ---- from OAI.Combinatorics.TriangleFace.Faces ----
namespace OAI

namespace CanonicalFace198

variable {A B : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B]

theorem self_mem (P : Set A) (x : A) : x ∈ minFace P x := by
  apply Set.mem_sInter.mpr
  intro F hF
  exact hF.2.2

theorem least {P F : Set A} {x : A} (hF : Convex ℝ F)
    (hPF : IsExtreme ℝ P F) (hxF : x ∈ F) : minFace P x ⊆ F := by
  intro y hy
  exact Set.mem_sInter.mp hy F ⟨hF, hPF, hxF⟩

theorem convex (P : Set A) (x : A) : Convex ℝ (minFace P x) := by
  exact convex_sInter (fun _ hF => hF.1)

theorem extreme {P : Set A} (hP : Convex ℝ P) {x : A} (hx : x ∈ P) :
    IsExtreme ℝ P (minFace P x) := by
  apply isExtreme_sInter
  · exact ⟨P, hP, IsExtreme.refl ℝ P, hx⟩
  · intro F hF
    exact hF.2.1

theorem extreme_affine_image (f : A →ᵃ[ℝ] B) (hf : Function.Injective f)
    {P Q : Set A} (h : IsExtreme ℝ P Q) : IsExtreme ℝ (f '' P) (f '' Q) := by
  refine ⟨Set.image_mono h.subset, ?_⟩
  rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ hseg
  rw [← image_openSegment ℝ f] at hseg
  obtain ⟨w',hw',he⟩ := hseg
  have hww : w' = w := hf he
  exact ⟨u, h.left_mem_of_mem_openSegment hu hv hw (hww ▸ hw'), rfl⟩

theorem extreme_affine_preimage (f : A →ᵃ[ℝ] B) {P : Set A} {Q R : Set B}
    (hPQ : f '' P ⊆ Q) (hQR : IsExtreme ℝ Q R) :
    IsExtreme ℝ P (P ∩ f ⁻¹' R) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro u hu v hv w hw hseg
  refine ⟨hu, hQR.left_mem_of_mem_openSegment (hPQ ⟨u,hu,rfl⟩)
    (hPQ ⟨v,hv,rfl⟩) hw.2 ?_⟩
  rw [← image_openSegment ℝ f]
  exact ⟨w,hseg,rfl⟩

theorem image_minFace (f : A →ᵃ[ℝ] B) (hf : Function.Injective f)
    {P : Set A} {K : Set B} (hP : Convex ℝ P) (hK : Convex ℝ K)
    (hface : IsExtreme ℝ K (f '' P)) {x : A} (hx : x ∈ P) :
    f '' minFace P x = minFace K (f x) := by
  have hfx : f x ∈ K := hface.subset ⟨x, hx, rfl⟩
  apply Set.Subset.antisymm
  · have hpreConvex : Convex ℝ (P ∩ f ⁻¹' minFace K (f x)) :=
      hP.inter ((convex K (f x)).affine_preimage f)
    have hpreExtreme := extreme_affine_preimage f hface.subset (extreme hK hfx)
    have hleast := least hpreConvex hpreExtreme ⟨hx, self_mem K (f x)⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (hleast hy).2
  · apply least ((convex P x).affine_image f)
    · exact hface.trans (extreme_affine_image f hf (extreme hP hx))
    · exact ⟨x, self_mem P x, rfl⟩

end CanonicalFace198

end OAI

-- ---- platform node ----
open OAI OAI.CanonicalFace198


theorem solution : type_of% @_root_.OAI.CanonicalFace198.image_minFace := @_root_.OAI.CanonicalFace198.image_minFace
