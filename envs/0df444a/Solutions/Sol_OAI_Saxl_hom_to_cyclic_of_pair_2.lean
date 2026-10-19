-- Prove2me | solution 2 for OAI.Saxl.hom_to_cyclic_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:03:26.583597+00:00
-- url     : https://prove2.me/submissions/fac98133-688c-40f2-af9b-9546afce0872

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SpechtDuality.lean:L120-L139
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.hom_to_cyclic_of_pair. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality

-- ---- from OAI.RepresentationTheory.Saxl.SpechtDuality ----
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- The ordinary bilinear coordinate pairing restricted to any invariant word subspace. -/
/- Complex conjugation-stable invariant word subspaces are canonically self-dual
via bilinear evaluation, yielding equivariant projections. -/
/- Actual self-duality of every complex Specht representation. -/
/- Restriction of the ambient bilinear coordinate pairing to an invariant subspace. -/
/- The genuine equivariant orthogonal-coordinate projection. -/
lemma subrepProject_pair {n d : ℕ} (S : Subrepresentation (wordRep n d))
    (hS : ∀ x ∈ S.toSubmodule, star x ∈ S.toSubmodule)
    (x : WordSpace n d) (y : S.toSubmodule) :
    dotProduct (subrepProject S hS x).val y.val = dotProduct x y.val := by
  have hh := (subrepSelfDual S hS).apply_symm_apply (subrepPairFromAmbient S x)
  exact congrArg (fun f : Module.Dual ℂ S.toSubmodule => f y) hh

/- A tensor power of a single letter-linear map, in ordinary word coordinates. -/
/- A nonzero contraction with a real cyclic vector gives an actual nonzero
intertwiner into its cyclic representation. -/
theorem hom_to_cyclic_of_pair {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule)
    (u : WordSpace n e) (hu : star u = u)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation
      (cyclic (wordRep n e) u).toRepresentation, f ≠ 0 := by
  let inc : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun g => rfl }
  let f := (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)).comp ((wordMap L).comp inc)
  refine ⟨f, ?_⟩
  intro hf
  have hp := subrepProject_pair (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx) (wordMap L x.val) ⟨u, mem_cyclic _ _⟩
  have he : f x = 0 := by rw [hf]; rfl
  change (subrepProject (cyclic (wordRep n e) u)
    (fun _ hx => cyclic_star u hu hx)) (wordMap L x.val) = 0 at he
  rw [he] at hp
  exact h (hp.symm.trans (zero_dotProduct _))

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.hom_to_cyclic_of_pair := @_root_.OAI.Saxl.hom_to_cyclic_of_pair
