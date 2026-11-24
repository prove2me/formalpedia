-- Prove2me | solution 1 for GlobalTheory.LocalInv.part_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:09.712888+00:00
-- url     : https://prove2.me/submissions/f620a04c-bef7-4192-b9a6-14e3033af74b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_NoLocalInvariants
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_TemperedRepresentations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_WeightRegularOfExt
import Theorems.Thm_GlobalTheory_LocalInv_r_odd
import Theorems.Thm_GlobalTheory_LocalInv_list_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LocalInv
open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
namespace GlobalTheory.LocalInv
theorem _root_.solution (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (P : A.AV i)
    (Pa : List (Part A.CG)) (hB : IsBCV N A i P Pa) (p : Part A.CG) (hp : p ∈ Pa) (ha : Odd p.a)
    (hd : Odd p.d) : A.csd (A.tw p.π A.etaT) ∧ A.ralg (A.tw p.π A.etaT) := by
  refine ⟨A.csd_tw _ _ hη.1 (hB.1 p hp).2.2, (A.ralg_def _).2 fun τ => ?_⟩
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
  obtain ⟨k0, hk0⟩ := hη.2 τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hle : (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ A.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd.pos)
  rw [A.infG_tw _ _ τ s hs]
  refine ⟨(Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle (hW i P τ).1)).map (add_left_injective s), ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  obtain ⟨a, ha⟩ := ha
  obtain ⟨d, hd⟩ := hd
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  refine ⟨k + k0 + r + t + 1 - d - a, ?_⟩
  rw [Ranks.nV, hr, ht, hd] at hk
  rw [hk0, ha]
  push_cast at hk ⊢
  linear_combination hk
end GlobalTheory.LocalInv
