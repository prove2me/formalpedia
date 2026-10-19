-- Prove2me | solution 1 for OAI.Problem313.blockEdgeOrbit_card_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:23:27.93299+00:00
-- url     : https://prove2.me/submissions/061bc9ae-b6bd-4f81-b5ac-542a44342dbc

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/BlockOrbits.lean:L143-L170
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.blockEdgeOrbit_card_lower. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_block_boundary_mem_orbit
import Theorems.Thm_OAI_Problem313_exists_block_perm_map

-- ---- from OAI.Combinatorics.SharpThreshold.BlockOrbits ----
namespace OAI

universe u

noncomputable section

namespace Problem313

/-- All edges wholly contained in a block are in one supported-permutation orbit. -/
theorem block_internal_mem_orbit {n : ℕ} {B : Finset (Fin n)}
    {e e' : GraphEdge n} (he : e.val ⊆ B) (he' : e'.val ⊆ B) :
    e' ∈ blockEdgeOrbit B e := by
  obtain ⟨π, hπ, hmap⟩ := exists_block_perm_map B e.val e'.val he he' (e.property.trans e'.property.symm)
  exact mem_blockEdgeOrbit.mpr ⟨π, hπ, Subtype.ext hmap⟩

/-- The number of graph edges wholly contained in a vertex block. -/
theorem card_block_internal_edges {n : ℕ} (B : Finset (Fin n)) :
    (Finset.univ.filter (fun e : GraphEdge n => e.val ⊆ B)).card = B.card.choose 2 := by
  classical
  rw [← Finset.card_powersetCard]
  apply Finset.card_bij (fun e _ => e.val)
  · intro e he
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp he).2, e.property⟩
  · intro e he e' he' h
    exact Subtype.ext h
  · intro s hs
    obtain ⟨hsB, hsc⟩ := Finset.mem_powersetCard.mp hs
    exact ⟨⟨s, hsc⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsB⟩, rfl⟩

theorem block_card_le_choose_two (m : ℕ) (hm : 3 ≤ m) : m ≤ m.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  exact Nat.mul_le_mul_left m (by omega)

/-- Internal edge orbits have at least as many edges as the block has vertices. -/
theorem block_internal_orbit_card {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} (hB : 3 ≤ B.card) (he : e.val ⊆ B) :
    B.card ≤ (blockEdgeOrbit B e).card := by
  classical
  calc
    B.card ≤ B.card.choose 2 := block_card_le_choose_two _ hB
    _ = (Finset.univ.filter (fun e' : GraphEdge n => e'.val ⊆ B)).card :=
      (card_block_internal_edges B).symm
    _ ≤ (blockEdgeOrbit B e).card := Finset.card_le_card (by
      intro e' he'
      exact block_internal_mem_orbit he (Finset.mem_filter.mp he').2)

theorem blockBoundaryEdge_injective {n : ℕ} {B : Finset (Fin n)}
    (w : Fin n) (hw : w ∉ B) : Function.Injective (blockBoundaryEdge w hw) := by
  intro u v h
  have he : ({u.val, w} : Finset (Fin n)) = {v.val, w} := congrArg Subtype.val h
  have hu : u.val ∈ ({v.val, w} : Finset (Fin n)) := by rw [← he]; simp
  rcases (show u.val = v.val ∨ u.val = w by simpa using hu) with huv | huw
  · exact Subtype.ext huv
  · exact False.elim (hw (huw ▸ u.property))

/-- Boundary edge orbits contain at least one edge for every block vertex. -/
theorem block_boundary_orbit_card {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} {u w : Fin n} (hu : u ∈ B) (hw : w ∉ B)
    (he : e.val = {u, w}) : B.card ≤ (blockEdgeOrbit B e).card := by
  classical
  let emb : B ↪ GraphEdge n := ⟨blockBoundaryEdge w hw, blockBoundaryEdge_injective w hw⟩
  calc
    B.card = (Finset.univ.map emb).card := by simp
    _ ≤ (blockEdgeOrbit B e).card := Finset.card_le_card (by
      intro e' he'
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp he'
      exact block_boundary_mem_orbit hu hw he v)

/-- Every edge incident with a block of at least three vertices has a
supported-permutation orbit of cardinality at least the block cardinality. -/
theorem blockEdgeOrbit_card_lower {n : ℕ} {B : Finset (Fin n)}
    {e : GraphEdge n} (hB : 3 ≤ B.card) (hmeet : (e.val ∩ B).Nonempty) :
    B.card ≤ (blockEdgeOrbit B e).card := by
  classical
  by_cases he : e.val ⊆ B
  · exact block_internal_orbit_card hB he
  obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp e.property
  by_cases ha : a ∈ B
  · have hb : b ∉ B := by
      intro hb
      apply he
      intro z hz
      rw [heab] at hz
      rcases (show z = a ∨ z = b by simpa using hz) with rfl | rfl
      · exact ha
      · exact hb
    exact block_boundary_orbit_card ha hb heab
  · have hb : b ∈ B := by
      obtain ⟨z, hz⟩ := hmeet
      obtain ⟨hze, hzB⟩ := Finset.mem_inter.mp hz
      rw [heab] at hze
      rcases (show z = a ∨ z = b by simpa using hze) with rfl | rfl
      · exact False.elim (ha hzB)
      · exact hzB
    apply block_boundary_orbit_card hb ha
    simpa [Finset.pair_comm] using heab

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.blockEdgeOrbit_card_lower := @_root_.OAI.Problem313.blockEdgeOrbit_card_lower
