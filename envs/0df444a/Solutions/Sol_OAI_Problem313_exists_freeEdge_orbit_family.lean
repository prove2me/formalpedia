-- Prove2me | solution 1 for OAI.Problem313.exists_freeEdge_orbit_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:25:06.831262+00:00
-- url     : https://prove2.me/submissions/5df31f68-1e1b-498b-9a21-3bd7c293674f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockOrbitSubtype.lean:L16-L36
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.exists_freeEdge_orbit_family. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Theorems.Thm_OAI_Problem313_blockEdgeOrbit_card_lower

-- ---- from OAI.Combinatorics.SharpThreshold.BlockOrbitSubtype ----
namespace OAI

noncomputable section
namespace Problem313

/-- The supported permutation orbit of a free edge consists only of free edges. -/
theorem blockEdgeOrbit_touches {n : ℕ} {B : Finset (Fin n)}
    {e d : GraphEdge n} (he : EdgeTouches B e) (hd : d ∈ blockEdgeOrbit B e) :
    EdgeTouches B d := by
  obtain ⟨π, hπ, rfl⟩ := mem_blockEdgeOrbit.mp hd
  exact (edgeTouches_permEdge_iff hπ e).mpr he

/-- A free edge has at least `B.card` free-edge orbit mates, with explicit
supported-permutation witnesses. This is the finite-coordinate interface for
conditional influence bounds. -/
theorem exists_freeEdge_orbit_family {n : ℕ} (B : Finset (Fin n))
    (hB : 3 ≤ B.card) (e : {e : GraphEdge n // EdgeTouches B e}) :
    ∃ S : Finset {d : GraphEdge n // EdgeTouches B d},
      B.card ≤ S.card ∧ ∀ d ∈ S, ∃ π : Equiv.Perm (Fin n),
        SupportedOnBlock B π ∧ permEdge π e.val = d.val := by
  classical
  let S := (blockEdgeOrbit B e.val).subtype (EdgeTouches B)
  have hmap : S.map (Function.Embedding.subtype _) = blockEdgeOrbit B e.val :=
    Finset.subtype_map_of_mem (fun d hd => blockEdgeOrbit_touches e.property hd)
  have hcard : S.card = (blockEdgeOrbit B e.val).card := by
    simpa using congrArg Finset.card hmap
  refine ⟨S, ?_, ?_⟩
  · rw [hcard]
    apply blockEdgeOrbit_card_lower hB
    obtain ⟨v, hve, hvB⟩ := e.property
    exact ⟨v, Finset.mem_inter.mpr ⟨hve, hvB⟩⟩
  · intro d hd
    exact mem_blockEdgeOrbit.mp (Finset.mem_subtype.mp hd)

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.exists_freeEdge_orbit_family := @_root_.OAI.Problem313.exists_freeEdge_orbit_family
