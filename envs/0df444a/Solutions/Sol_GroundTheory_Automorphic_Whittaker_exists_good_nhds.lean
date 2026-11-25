-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.exists_good_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:48:15.668409+00:00
-- url     : https://prove2.me/submissions/80367cb9-0eb0-47d8-8218-e1bcc8316c92

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaL_sigmaL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_relSpan_mono
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigmaL_mem_relSpan
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_goodSub
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_cellGe
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_cellGe_of_eq
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_smul_mem_cellGe
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_eq_of_not_irrelevant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cell_irrelevant
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_cell_relevant
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_diag_perm
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_iff
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_llRank_le
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_sigma_mem_doubleCoset_permGL
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_supportedIn_le_of_local
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
attribute [local instance] biAction
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
attribute [local instance] totallyDisconnectedSpace_localField
attribute [local instance] continuousSMul_biAction
variable (ψ₀ : AddChar F ℂ)
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) (x : GL (Fin n) F) :
    ∃ V : Set (GL (Fin n) F), IsOpen V ∧ x ∈ V ∧ supportedIn V ≤ goodSub n ψ₀ := by
  by_contra hx
  set S : Set (GL (Fin n) F) :=
    {y | ¬ ∃ V : Set (GL (Fin n) F), IsOpen V ∧ y ∈ V ∧ supportedIn V ≤ goodSub n ψ₀}
  set Φ : GL (Fin n) F → ℕ := fun y => ∑ i, ∑ j, llRank i j y
  have hS : S.Nonempty := ⟨x, hx⟩
  have hbdd : BddAbove (Φ '' S) := by
    refine ⟨n * (n * n), ?_⟩
    rintro _ ⟨y, -, rfl⟩
    calc Φ y ≤ ∑ _i : Fin n, ∑ _j : Fin n, n :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => llRank_le i j y
      _ = n * (n * n) := by simp
  obtain ⟨g, hgS, hgmax⟩ : ∃ g ∈ S, ∀ y ∈ S, Φ y ≤ Φ g := by
    obtain ⟨g, hg, hgeq⟩ := Nat.sSup_mem (hS.image Φ) hbdd
    exact ⟨g, hg, fun y hy => hgeq ▸ le_csSup hbdd ⟨y, hy, rfl⟩⟩
  apply hgS
  set w := bruhatCell g with hw
  have hlarger : ∀ y ∈ cellGe g, y ∉ cellLe g →
      ∃ V : Set (GL (Fin n) F), IsOpen V ∧ y ∈ V ∧ supportedIn V ≤ goodSub n ψ₀ := by
    intro y hy1 hy2
    by_contra hyS
    have hle := hgmax y hyS
    simp only [cellLe, Set.mem_ofPred_eq, not_forall, not_le] at hy2
    obtain ⟨i, j, hij⟩ := hy2
    have hlt : Φ g < Φ y :=
      Finset.sum_lt_sum (fun i _ => Finset.sum_le_sum fun j _ => hy1 i j)
        ⟨i, Finset.mem_univ _, Finset.sum_lt_sum (fun j _ => hy1 i j) ⟨j, Finset.mem_univ _, hij⟩⟩
    omega
  have hinvGe : ∀ k : NN F n, ∀ y ∈ cellGe g, k • y ∈ cellGe g := fun k y hy => smul_mem_cellGe k hy
  have hRR : ∀ {r : GL (Fin n) F → ℂ} {U : Set (GL (Fin n) F)}, r ∈ relSpan (chi (n := n) ψ₀) U →
      r ∈ rel n ψ₀ := fun hr => relSpan_mono (subset_univ _) hr
  have hσR : ∀ {r : GL (Fin n) F → ℂ} {U : Set (GL (Fin n) F)}, r ∈ relSpan (chi (n := n) ψ₀) U →
      sigmaL r ∈ rel n ψ₀ := fun hr => relSpan_mono (subset_univ _) (sigmaL_mem_relSpan ψ₀ hr)
  by_cases hA : ∀ h : GL (Fin n) F, bruhatCell h = w → bruhatCell (sigma h) = w
  ·
    set U := cellGe g ∩ sigma ⁻¹' cellGe g with hUdef
    have hUo : IsOpen U := (isOpen_cellGe g).inter ((isOpen_cellGe g).preimage continuous_sigma)
    have hUinv : ∀ k : NN F n, ∀ y ∈ U, k • y ∈ U := fun k y hy =>
      ⟨smul_mem_cellGe k hy.1, by
        show sigma (k • y) ∈ cellGe g
        rw [sigma_smul]
        exact smul_mem_cellGe _ hy.2⟩
    have hcellU : ∀ h, bruhatCell h = bruhatCell g → h ∈ U := fun h hh =>
      ⟨mem_cellGe_of_eq hh, mem_cellGe_of_eq (hA h hh)⟩
    have hUσ : ∀ y, sigma y ∈ U ↔ y ∈ U := fun y => by
      show sigma y ∈ cellGe g ∧ sigma (sigma y) ∈ cellGe g ↔ y ∈ cellGe g ∧ sigma y ∈ cellGe g
      rw [sigma_sigma, and_comm]
    refine ⟨U, hUo, hcellU g rfl, ?_⟩
    have hgood : supportedIn (U \ cellLe g) ≤ goodSub n ψ₀ :=
      supportedIn_le_of_local fun y hy => hlarger y hy.1.1 hy.2
    intro f hf
    have hmem := cell_relevant ψ₀ hψ hψ₁ hUo hUinv inter_subset_left hcellU hUσ hA hf
    obtain ⟨r, hr, k, hk, hrk⟩ := Submodule.mem_sup.1 hmem
    have hk' : k ∈ supportedIn (U \ cellLe g) :=
      ⟨hk.1.1, fun y hy => ⟨hk.1.2 hy, fun hyC => hy (hk.2 y hyC)⟩⟩
    have hkgood := (mem_goodSub ψ₀).1 (hgood hk')
    have hneg : sigmaL r + sigmaL k = -(r + k) := by
      rw [← map_add, hrk, map_sub, sigmaL_sigmaL]
      abel
    have hsum : k + sigmaL k ∈ rel n ψ₀ := by
      have e : k + sigmaL k = -(r + sigmaL r) := by
        rw [← sub_eq_zero]
        rw [← sub_eq_zero] at hneg
        have h2 : k + sigmaL k - -(r + sigmaL r) = sigmaL r + sigmaL k - -(r + k) := by abel
        rw [h2, hneg]
      rw [e]
      exact neg_mem (add_mem (hRR hr) (hσR hr))
    have hk2 : (2 : ℂ) • k ∈ rel n ψ₀ := by
      have e : (2 : ℂ) • k = (k + sigmaL k) + (k - sigmaL k) := by
        rw [two_smul]
        abel
      rw [e]
      exact add_mem hsum hkgood
    have hkR : k ∈ rel n ψ₀ := by
      have := (rel n ψ₀).smul_mem (1 / 2 : ℂ) hk2
      rwa [smul_smul, one_div, inv_mul_cancel₀ two_ne_zero, one_smul] at this
    rw [mem_goodSub, ← hrk]
    exact add_mem (hRR hr) hkR
  ·
    push Not at hA
    obtain ⟨h₀, hh₀, hσh₀⟩ := hA
    have hirr : ∀ t, Irrelevant ψ₀ w t := by
      intro t
      by_contra hrel
      have hfix := sigma_eq_of_not_irrelevant ψ₀ hψ₁ hrel
      apply hσh₀
      have e₁ : bruhatCell (sigma h₀) = Fin.revPerm * w⁻¹ * Fin.revPerm :=
        bruhatCell_eq_iff.2 (sigma_mem_doubleCoset_permGL (bruhatCell_eq_iff.1 hh₀))
      have e₂ : bruhatCell (sigma (Iwasawa.diagGL F n t * permGL F w)) =
          Fin.revPerm * w⁻¹ * Fin.revPerm :=
        bruhatCell_eq_iff.2 (sigma_mem_doubleCoset_permGL
          (bruhatCell_eq_iff.1 (bruhatCell_diag_perm t w)))
      rw [hfix, bruhatCell_diag_perm] at e₂
      rw [e₁, ← e₂]
    refine ⟨cellGe g, isOpen_cellGe g, mem_cellGe_of_eq rfl, ?_⟩
    have hgood : supportedIn (cellGe g \ cellLe g) ≤ goodSub n ψ₀ :=
      supportedIn_le_of_local fun y hy => hlarger y hy.1 hy.2
    intro f hf
    have hmem := cell_irrelevant ψ₀ hψ (isOpen_cellGe g) hinvGe subset_rfl
      (fun h hh => mem_cellGe_of_eq hh) hirr hf
    obtain ⟨r, hr, k, hk, rfl⟩ := Submodule.mem_sup.1 hmem
    have hk' : k ∈ supportedIn (cellGe g \ cellLe g) :=
      ⟨hk.1.1, fun y hy => ⟨hk.1.2 hy, fun hyC => hy (hk.2 y hyC)⟩⟩
    rw [mem_goodSub]
    have e : r + k - sigmaL (r + k) = (r - sigmaL r) + (k - sigmaL k) := by
      rw [map_add]
      abel
    rw [e]
    exact add_mem (sub_mem (hRR hr) (hσR hr)) ((mem_goodSub ψ₀).1 (hgood hk'))
end GroundTheory.Automorphic.Whittaker
