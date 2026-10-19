-- Prove2me | solution 2 for OAI.Saxl.columnAlt_tabloid
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:00:01.815442+00:00
-- url     : https://prove2.me/submissions/c86f4782-eb53-415e-9f3d-5017c47b8d19

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SpechtSubmodule.lean:L52-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.columnAlt_tabloid. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Theorems.Thm_OAI_Saxl_columnAlt_single

-- ---- from OAI.RepresentationTheory.Saxl.SpechtSubmodule ----
namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV

namespace Saxl

/- The actual row-tabloid permutation module, embedded in the word space. -/
/- The Ferrers shape forces the column antisymmetrizer to have rank one
on the row-tabloid module. -/
lemma columnAlt_tabloid {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    {x : WordSpace n (μ.colLen 0)} (hx : x ∈ tabloidSub t) :
    columnAlt t x ∈ Submodule.span ℂ {polytabloid t} := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    dsimp only
    rw [wordRep_single]
    exact columnAlt_single t g⁻¹
  | zero => simpa only [map_zero] using (Submodule.zero_mem (Submodule.span ℂ {polytabloid t}))
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem _ c ih

/- On words, precomposition by a position permutation is a bijection. -/
/- Every nonzero vector in the genuine complex Specht cyclic subspace
again generates that whole subspace. -/
/- Inclusion of a subrepresentation of a subrepresentation into the ambient space. -/
/- The complex polytabloid module is irreducible. -/
end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.columnAlt_tabloid := @_root_.OAI.Saxl.columnAlt_tabloid
