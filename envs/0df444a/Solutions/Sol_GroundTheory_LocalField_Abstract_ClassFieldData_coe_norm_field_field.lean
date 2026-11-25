-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.ClassFieldData.coe_norm_field_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:48:28.524503+00:00
-- url     : https://prove2.me/submissions/d07f6aea-8395-4fc2-a861-84abcccbd258

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_field_le_field_of_pow
import Theorems.Thm_GroundTheory_LocalField_Abstract_ClassFieldData_FrobeniusLift_field_inf_ker
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_eq_prod_smul_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm_of_le
import Theorems.Thm_GroundTheory_LocalField_Abstract_fixedModule_anti
import Theorems.Thm_GroundTheory_LocalField_Abstract_le_frobeniusClosure
import Theorems.Thm_GroundTheory_LocalField_Abstract_map_frobeniusClosure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
open GroundTheory.LocalField.Abstract.ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
namespace GroundTheory.LocalField.Abstract.ClassFieldData
theorem _root_.solution (s1 s2 : D.FrobeniusLift K) (k : ℕ) (hk : 0 < k)
    (h2 : s2.elt = s1.elt ^ k) (hdeg : s2.deg = k * s1.deg)
    (z : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) z : A) =
      ∏ i : Fin k, s1.elt ^ (i : ℕ) • (z : A) := by
  have hmap1 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s1.mem)
    s1.deg_eq (L := (L : Subgroup G))
  have hmap2 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s2.mem)
    s2.deg_eq (L := (L : Subgroup G))
  rw [hdeg, mul_assoc] at hmap2
  have hf : 0 < s1.deg * inertiaDegree D.deg K :=
    Nat.mul_pos s1.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
  have key := coe_norm_eq_prod_smul_norm D.deg (K := ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (S := ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) (J := (L : Subgroup G) ⊓ D.deg.ker)
    (f := s1.deg * inertiaDegree D.deg K) (n := k) hk hf
    (fun x hx => field_le_field_of_pow hLK s1 s2 k h2 hx) ?_ ?_ ?_ ?_
    (s1.elt_mem_field hLK) s1.deg_eq z (fixedModule_anti le_frobeniusClosure z.2)
  · rw [key]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    exact coe_norm_of_le (fun x hx => (s1.field_inf_ker hLK).le hx) _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s2.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap2] at this
    exact this
  · intro x _ hx
    have : D.deg x ∈ AddSubgroup.toSubgroup (multiples (k * (s1.deg * inertiaDegree D.deg K))) := hx
    rw [← hmap2] at this
    obtain ⟨y, hy, hyx⟩ := this
    exact ⟨y, hy, hyx⟩
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s1.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap1] at this
    exact this
  · intro q hq
    have hqJ : q ∈ (L : Subgroup G) ⊓ D.deg.ker := (s1.field_inf_ker hLK).le hq
    exact ⟨fun _ => hqJ, fun h => le_frobeniusClosure h⟩
end GroundTheory.LocalField.Abstract.ClassFieldData
