-- Prove2me | solution 1 for OAI.Saxl.hom_to_cyclic_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:18:10.351226+00:00
-- url     : https://prove2.me/submissions/fb2450c3-a753-47da-9c34-8f7df248be0f

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality

open OAI OAI.Saxl
open scoped TensorProduct


theorem solution {n d e : ℕ} (L : Fin d → Fin e → ℂ)
    (S : Subrepresentation (wordRep n d)) (x : S.toSubmodule)
    (u : WordSpace n e) (hu : star u = u)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ f : Representation.IntertwiningMap S.toRepresentation
      (cyclic (wordRep n e) u).toRepresentation, f ≠ 0 := by
  classical
  let U := cyclic (wordRep n e) u
  have hU : ∀ y ∈ U.toSubmodule, star y ∈ U.toSubmodule :=
    fun _ hy => cyclic_star _ hu hy
  let ι : Representation.IntertwiningMap S.toRepresentation (wordRep n d) :=
    ⟨S.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  refine ⟨(subrepProject U hU).comp ((wordMap L).comp ι), ?_⟩
  intro hf
  have h1 := congrArg (fun f => f x) hf
  change (subrepSelfDual U hU).symm.toIntertwiningMap
    (subrepPairFromAmbient U (wordMap L x.val)) = 0 at h1
  rw [← Representation.Equiv.toLinearEquiv_apply,
    LinearEquiv.map_eq_zero_iff] at h1
  have h2 := congrArg (fun φ : Module.Dual ℂ U.toSubmodule => φ ⟨u, mem_cyclic _ _⟩) h1
  exact h h2

