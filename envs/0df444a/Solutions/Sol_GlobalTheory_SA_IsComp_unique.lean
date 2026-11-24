-- Prove2me | solution 1 for GlobalTheory.SA.IsComp.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:14.822384+00:00
-- url     : https://prove2.me/submissions/de633adb-72e5-4ff3-9cf7-629b20ef583b

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Theorems.Thm_GlobalTheory_SA_X_le_xPlus
import Theorems.Thm_GlobalTheory_SA_z_mem_xPlus
import Theorems.Thm_GlobalTheory_SA_eq_zero_of_smul_z_mem
import Theorems.Thm_GlobalTheory_SA_isComp_iff
import Theorems.Thm_GlobalTheory_SA_IsComp_swap
import Theorems.Thm_GlobalTheory_SA_IsComp_sub
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
variable {R K V : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K] [AddCommGroup V] [Module K V]
  [Module R V] [IsScalarTower R K V] {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.SA
namespace IsComp
theorem _root_.solution {F F' : FlagD H r} (hd : Disjoint (xPlus F) (xPlus F')) {u : V} {a a' b b' : K}
    (h : IsComp F F' u a a') (k : IsComp F F' u b b') : a = b ∧ a' = b' := by
  have key : ∀ {G G' : FlagD H r} {c c' : K}, Disjoint (xPlus G) (xPlus G') → IsComp G G' 0 c c' → c = 0 := by
    intro G G' c c' hG hc
    obtain ⟨ξ, hξ, ξ', hξ', e⟩ := (isComp_iff _ _ _ _ _).1 hc
    have h1 : ξ + c • G.z ∈ xPlus G := add_mem (X_le_xPlus G hξ) (Submodule.smul_mem _ c (z_mem_xPlus G))
    have h2 : ξ + c • G.z ∈ xPlus G' := by
      rw [add_assoc (ξ + c • G.z)] at e
      rw [eq_neg_of_add_eq_zero_left e.symm]
      exact neg_mem (add_mem (X_le_xPlus G' hξ') (Submodule.smul_mem _ c' (z_mem_xPlus G')))
    have h3 := Submodule.disjoint_def.1 hG _ h1 h2
    refine eq_zero_of_smul_z_mem G ?_
    rw [eq_neg_of_add_eq_zero_right h3]
    exact neg_mem hξ
  have h0 := h.sub k
  rw [sub_self] at h0
  exact ⟨sub_eq_zero.1 (key hd h0), sub_eq_zero.1 (key hd.symm h0.swap)⟩
end IsComp
end GlobalTheory.SA
