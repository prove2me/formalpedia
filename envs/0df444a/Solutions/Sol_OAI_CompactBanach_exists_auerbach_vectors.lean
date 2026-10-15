-- Prove2me | solution 1 for OAI.CompactBanach.exists_auerbach_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T07:17:54.328694+00:00
-- url     : https://prove2.me/submissions/0fe31832-ec1a-4a9b-adb9-feb2f3543408

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Auerbach.lean:L70-L93
-- (upload_full_project.md Phase 4): solution for node OAI.CompactBanach.exists_auerbach_vectors. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Theorems.Thm_OAI_CompactBanach_exists_auerbach_basis

-- ---- from OAI.Geometry.DoublingHilbert.Auerbach ----
namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach

                                                                                       
theorem exists_auerbach_vectors {B ι : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [Fintype ι] (hB : ¬ FiniteDimensional ℝ B) :
    ∃ v : ι → B, (∀ i, ‖v i‖ ≤ 1) ∧
      ∀ (c : ι → ℝ) i, |c i| ≤ ‖∑ j, c j • v j‖ := by
  classical
  let I := Module.Basis.ofVectorSpaceIndex ℝ B
  let e : Module.Basis I ℝ B := Module.Basis.ofVectorSpace ℝ B
  have : Infinite I := not_finite_iff_infinite.mp (by
    intro h
    let := h
    exact hB (Module.Finite.of_basis e))
  let f : ι → I := fun i => Infinite.natEmbedding I ((Fintype.equivFin ι) i).val
  have hf : Function.Injective f :=
    (Infinite.natEmbedding I).injective.comp (Fin.val_injective.comp (Fintype.equivFin ι).injective)
  have hli : LinearIndependent ℝ (e ∘ f) := e.linearIndependent.comp f hf
  let V := Submodule.span ℝ (Set.range (e ∘ f))
  let eV : Module.Basis ι ℝ V := Module.Basis.span hli
  let : FiniteDimensional ℝ V := Module.Finite.of_basis eV
  obtain ⟨b, hb, hc⟩ := exists_auerbach_basis eV
  refine ⟨fun i => (b i : B), hb, ?_⟩
  intro c i
  have h := hc (∑ j, c j • b j) i
  rw [b.repr_sum_self] at h
  simpa only [← Submodule.coe_smul, ← Submodule.coe_sum, Submodule.norm_coe] using h

end CompactBanach
end

end OAI

-- ---- platform node ----
open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.CompactBanach.exists_auerbach_vectors := @_root_.OAI.CompactBanach.exists_auerbach_vectors
