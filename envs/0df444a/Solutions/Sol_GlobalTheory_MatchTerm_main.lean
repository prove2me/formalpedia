-- Prove2me | solution 1 for GlobalTheory.MatchTerm.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:24:11.10932+00:00
-- url     : https://prove2.me/submissions/996c9d67-97a6-47ca-af57-f47875f10daa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaMatchingExistsRightTorusTorsion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationSeriesTermsNestStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionLatticeIsoAndTermsAgree
import Theorems.Thm_GlobalTheory_MatchTerm_txT_tendsto
import Theorems.Thm_GlobalTheory_MatchTerm_exists_txT_ne
import Theorems.Thm_GlobalTheory_MatchTerm_twisted_eq
import Theorems.Thm_GlobalTheory_MatchTerm_Cl_add
import Theorems.Thm_GlobalTheory_MatchTerm_Cl_cong
import Theorems.Thm_GlobalTheory_MatchTerm_Cl_down
import Theorems.Thm_GlobalTheory_MatchTerm_Cl_shift
import Theorems.Thm_GlobalTheory_MatchTerm_Cl_tor
import Theorems.Thm_GlobalTheory_MatchTerm_class_sum_eq
import Theorems.Thm_GlobalTheory_MatchTerm_cotot_G
import Theorems.Thm_GlobalTheory_MatchTerm_exists_torus_bij
import Theorems.Thm_GlobalTheory_MatchTerm_limit_class
import Theorems.Thm_GlobalTheory_MatchTerm_tot_G
import Theorems.Thm_GlobalTheory_T_degenerationData_torsion_structure_algClosed
import Theorems.Thm_GlobalTheory_existsUnique_addEquiv_of_compatible_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex Filter
open scoped BigOperators Topology
open GlobalTheory GlobalTheory.MatchTerm
namespace GlobalTheory.MatchTerm
theorem _root_.solution : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  intro C _ _ _ _ N N' q q' n g g' hpr hn hn1 hq hq' hT hT' μ hA
  have hC : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn1
    exact zero_ne_one hn1
  have hn0 := hpr.ne_zero
  have key : ∀ i j (p : N.QT ((n ^ j) ^ 2)) (p' : N'.QT ((n ^ j) ^ 2)), μ.r _ p p' → p.1.1 = 1 → p'.1.1 = 1 →
      ∀ α α', Cl μ i α α' →
      ∑' z, N'.txT (n ^ j) p' (α' + n ^ i • z) = μ.c₀ * ∑' z, N.txT (n ^ j) p (α + n ^ i • z) := by
    intro i j p p' h hp hp' α α' hα
    obtain ⟨E, hE, hr⟩ := exists_torus_bij μ hn0 hA ⟨i, rfl⟩
    exact class_sum_eq (by rw [Nat.cast_pow, norm_pow, hn1, one_pow]) _ _ (txT_tendsto hq hn.pow p hp)
      (txT_tendsto hq' hn.pow p' hp') _ α α' E hE (fun t => hα.tor μ (hr t))
      fun t => twisted_eq μ hn hC hT hA i j h hp hp' (hr t)
  have tot : ∀ j x, ∃ x', Cl μ j x x' := fun j x => by
    obtain ⟨p, hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hC hT j).2.2.1 x
    obtain ⟨p', h⟩ := μ.tot j p
    exact ⟨_, p, p', h, hp, rfl⟩
  have cotot : ∀ j x', ∃ x, Cl μ j x x' := fun j x' => by
    obtain ⟨p', hp⟩ := (GlobalTheory.T.degenerationData_torsion_structure_algClosed C N' n g' hC hT' j).2.2.1 x'
    obtain ⟨p, h⟩ := μ.cotot j p'
    exact ⟨_, p, p', h, rfl, hp⟩
  have hL : ∃ a, (n ^ 1) ^ 2 = n ^ a := ⟨2, by ring⟩
  have hf : ∀ x, ∃ x', ∀ j, Cl μ j x x' := fun x => by
    choose α hα using fun j => tot j x
    obtain ⟨p, hp, hx⟩ := exists_txT_ne hq hn hC hT x
    obtain ⟨p', h, hp'⟩ := tot_G μ hA hL p hp
    obtain ⟨x', hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
      μ.c₀ x α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).1 ⟨0, by simp⟩)
      fun i => key i 1 p p' h hp hp' _ _ (hα i)).2 (mul_ne_zero μ.c₀_ne hx)
    refine ⟨x', fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ 0 z
  have hg : ∀ x', ∃ x, ∀ j, Cl μ j x x' := fun x' => by
    choose α hα using fun j => cotot j x'
    obtain ⟨p', hp', hx⟩ := exists_txT_ne hq' hn hC hT' x'
    obtain ⟨p, h, hp⟩ := cotot_G μ hA hL p' hp'
    obtain ⟨x, hx'⟩ := (limit_class hpr.two_le _ _ (txT_tendsto hq' hn.pow p' hp') (txT_tendsto hq hn.pow p hp)
      μ.c₀⁻¹ x' α (fun j => ((hα j).cong μ hA ((hα (j + 1)).down μ hn0)).2 ⟨0, by simp⟩)
      fun i => by rw [key i 1 p p' h hp hp' _ _ (hα i), inv_mul_cancel_left₀ μ.c₀_ne]).2
      (mul_ne_zero (inv_ne_zero μ.c₀_ne) hx)
    refine ⟨x, fun j => ?_⟩
    obtain ⟨z, hz⟩ := hx' j
    simpa [← hz] using (hα j).shift μ z 0
  obtain ⟨e, he, -⟩ := existsUnique_addEquiv_of_compatible_congr N.X N'.X n hpr.two_le (Cl μ) tot cotot
    (fun _ _ _ _ _ h h' => h.add μ h') (fun _ _ _ _ _ h h' => h.cong μ hA h') (fun _ _ _ _ _ h => h.shift μ _ _) hf hg
  refine ⟨e, fun j p p' h => ((he j _).cong μ hA ⟨p, p', h, rfl, rfl⟩).1 ⟨0, by simp⟩, fun j p p' h hp hp' χ => ?_⟩
  exact (limit_class hpr.two_le _ _ (txT_tendsto hq hn.pow p hp) (txT_tendsto hq' hn.pow p' hp')
    μ.c₀ χ (fun _ => e χ) (fun j => ⟨0, by simp⟩) fun i => key i j p p' h hp hp' _ _ (he i χ)).1 _
    fun j => ⟨0, by simp⟩
end GlobalTheory.MatchTerm
