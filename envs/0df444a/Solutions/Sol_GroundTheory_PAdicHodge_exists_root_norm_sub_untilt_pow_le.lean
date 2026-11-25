-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_root_norm_sub_untilt_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:23.236466+00:00
-- url     : https://prove2.me/submissions/e647e5d4-e03b-47db-9d08-5455ad099987

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_TiltAlgebra
import Definitions.Def_GroundTheory_PAdicHodge_AxLemma
import Definitions.Def_GroundTheory_PAdicHodge_UntiltApproxLemmas
import Theorems.Thm_GroundTheory_PAdicHodge_exists_multiset_eq_prod
import Theorems.Thm_GroundTheory_PAdicHodge_norm_prod_sub_untilt_le
import Theorems.Thm_GroundTheory_PAdicHodge_monic_monicOfCoeffs
import Theorems.Thm_GroundTheory_PAdicHodge_coeff_monicOfCoeffs
import Theorems.Thm_GroundTheory_PAdicHodge_natDegree_monicOfCoeffs
import Theorems.Thm_GroundTheory_PAdicHodge_exists_pow_card_le_of_prod_le
import Theorems.Thm_GroundTheory_PAdicHodge_norm_multiset_prod_eq
import Theorems.Thm_GroundTheory_PAdicHodge_tiltMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.tiltMap_algebraMap



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial
variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField C p]
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪C♭" => PreTilt (normInteger C) p
namespace GroundTheory.PAdicHodge
theorem _root_.solution [IsAlgClosed C♭] {Q : (normInteger C)[X]}
    (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (a : ℕ → 𝒪C♭)
    (ha : ∀ m < Q.natDegree, Ideal.Quotient.mk (Ideal.span {(p : normInteger C)}) (Q.coeff m) =
      PreTilt.coeff 0 (a m))
    {z : normInteger C} (hz : Q.eval z = 0) :
    ∃ b : 𝒪C♭, (monicOfCoeffs Q.natDegree a).eval b = 0 ∧
      ‖(z : C) - ((PreTilt.untilt b : normInteger C) : C)‖ ^ Q.natDegree ≤ ‖(p : C)‖ := by
  set e := Q.natDegree
  obtain ⟨s, hs⟩ := exists_multiset_eq_prod (monic_monicOfCoeffs (C := C) (p := p) e a)
  have hcard : Multiset.card s = e := by
    have := natDegree_monicOfCoeffs (C := C) (p := p) e a
    rw [hs, natDegree_multiset_prod_X_sub_C_eq_card] at this
    exact this
  have hQ' : Q.map (Ideal.Quotient.mk (Ideal.span {(p : normInteger C)})) =
      ((s.map fun b => X - Polynomial.C b).prod).map (PreTilt.coeff 0) := by
    rw [← hs]
    ext m
    rw [coeff_map, coeff_map, coeff_monicOfCoeffs]
    split_ifs with h1 h2
    · subst h1; rw [hQ.coeff_natDegree, map_one, map_one]
    · exact ha m h2
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero]
  have hprod := norm_prod_sub_untilt_le s hQ' hz
  rw [norm_multiset_prod_eq, Multiset.map_map] at hprod
  have hs0 : s ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hcard; omega
  obtain ⟨b, hb, hbl⟩ := exists_pow_card_le_of_prod_le hs0 (fun _ _ => norm_nonneg _) hprod
  refine ⟨b, ?_, by rwa [hcard] at hbl⟩
  rw [hs, eval_multiset_prod]
  exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map.2 ⟨b, hb, rfl⟩,
    by simp⟩)
end GroundTheory.PAdicHodge
