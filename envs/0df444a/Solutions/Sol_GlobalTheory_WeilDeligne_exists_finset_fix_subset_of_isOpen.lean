-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:39:23.106723+00:00
-- url     : https://prove2.me/submissions/102f51ad-0b04-4a91-a142-3327df1fe415

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingSubsetOpenInertiaSubgroup
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory GlobalTheory.WeilDeligne
namespace GlobalTheory.WeilDeligne
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)),
    IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A,
      (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  intro E Ω _ _ _ _ _ A M hM
  obtain ⟨U, hU, hUM⟩ := isOpen_induced_iff.mp hM
  have h1 : (1 : G E Ω) ∈ U := by
    have : (1 : Ine (F := E) A) ∈ (Subtype.val ⁻¹' U) := by rw [hUM]; exact M.one_mem
    simpa using this
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds h1)
  have hfg : L.toSubalgebra.FG := by
    apply Subalgebra.fg_of_fg_toSubmodule
    exact Module.Finite.iff_fg.mp hL
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun σ hσ => ?_⟩
  have hmem : (σ : G E Ω) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ∈ Algebra.adjoin E (t : Set Ω) := by rw [ht]; exact hx
    have key : Set.EqOn ((σ : G E Ω) : Ω →ₐ[E] Ω) (AlgHom.id E Ω) (Algebra.adjoin E (t : Set Ω)) :=
      AlgHom.eqOn_adjoin_iff.mpr (fun y hy => hσ y hy)
    exact key hx'
  have : σ ∈ (Subtype.val ⁻¹' U : Set (Ine (F := E) A)) := hLU hmem
  rw [hUM] at this
  exact this
end GlobalTheory.WeilDeligne
