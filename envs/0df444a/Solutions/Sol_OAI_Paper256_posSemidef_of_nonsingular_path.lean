-- Prove2me | solution 1 for OAI.Paper256.posSemidef_of_nonsingular_path
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:30:50.390093+00:00
-- url     : https://prove2.me/submissions/967b5e71-cd6c-4b99-89f7-cd32d9ac5290

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PositivePath.lean:L12-L45
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.posSemidef_of_nonsingular_path. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Definitions.Def_OAI_Analysis_HyperbolicCones_Coordinates
import Definitions.Def_OAI_Analysis_HyperbolicCones_ConeMatrix
import Theorems.Thm_OAI_Paper256_isClosed_posSemidef
import Theorems.Thm_OAI_Paper256_isOpen_posDef

-- ---- from OAI.Analysis.HyperbolicCones.PencilTopology ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

theorem posSemidef_of_tendsto {α : Type u} {f : Filter α} [f.NeBot] {n : ℕ}
    {A : α → Sym n} {H : Sym n} (hA : Tendsto A f (𝓝 H))
    (h : ∀ᶠ x in f, (A x : Mat n ℝ).PosSemidef) : (H : Mat n ℝ).PosSemidef :=
  (isClosed_posSemidef n).mem_of_tendsto hA h

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PositivePath ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256

/-- A continuous symmetric matrix path with no singularities at positive times
cannot change from indefinite to positive definite. -/
theorem posSemidef_of_nonsingular_path {n : ℕ} (F : ℝ → Sym n)
    (hF : ContinuousOn F (Ici 0)) (hF0 : ContinuousAt F 0)
    (hunit : ∀ t : ℝ, 0 < t → IsUnit (F t : Mat n ℝ))
    (hpos : ∃ t : ℝ, 0 < t ∧ (F t : Mat n ℝ).PosDef) :
    (F 0 : Mat n ℝ).PosSemidef := by
  let : PreconnectedSpace (Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  have hc : Continuous (fun t : Ioi (0 : ℝ) => F t) :=
    continuousOn_iff_continuous_domRestrict.mp (hF.mono Ioi_subset_Ici_self)
  let S : Set (Ioi (0 : ℝ)) := {t | (F t : Mat n ℝ).PosSemidef}
  have hclosed : IsClosed S := (isClosed_posSemidef n).preimage hc
  have heq : S = {t : Ioi (0 : ℝ) | (F t : Mat n ℝ).PosDef} := by
    ext t
    constructor
    · intro ht
      exact ht.posDef_iff_isUnit.mpr (hunit t t.property)
    · exact fun ht => ht.posSemidef
  have hopen : IsOpen S := by
    rw [heq]
    exact (isOpen_posDef n).preimage hc
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, hFt⟩ := hpos
    exact ⟨⟨t, ht⟩, hFt.posSemidef⟩
  have hSuniv : S = univ := (show IsClopen S from ⟨hclosed, hopen⟩).eq_univ hSne
  have hall : ∀ t : ℝ, 0 < t → (F t : Mat n ℝ).PosSemidef := by
    intro t ht
    have hm : (⟨t, ht⟩ : Ioi (0 : ℝ)) ∈ S := by rw [hSuniv]; trivial
    exact hm
  apply posSemidef_of_tendsto (f := 𝓝[Ioi (0 : ℝ)] 0)
    (hF0.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hall t ht

end Paper256

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256
open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.posSemidef_of_nonsingular_path := @_root_.OAI.Paper256.posSemidef_of_nonsingular_path
