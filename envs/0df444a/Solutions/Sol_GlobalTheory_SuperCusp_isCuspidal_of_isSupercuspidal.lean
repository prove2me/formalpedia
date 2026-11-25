-- Prove2me | solution 1 for GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:55.276258+00:00
-- url     : https://prove2.me/submissions/cf2a8a51-07fd-427f-8248-0e9acba1d58d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
import Theorems.Thm_GlobalTheory_SuperCusp_exists_dual_infinite
import Theorems.Thm_GlobalTheory_SuperCusp_exists_smooth_form_eq
import Theorems.Thm_GlobalTheory_SuperCusp_false_of_infinite
import Theorems.Thm_GlobalTheory_CentralExponent_cong_contract
import Theorems.Thm_GlobalTheory_CentralExponent_cong_factor
import Theorems.Thm_GlobalTheory_CentralExponent_exists_cong_subset
import Theorems.Thm_GlobalTheory_CentralExponent_exists_nabs_lt_one
import Theorems.Thm_GlobalTheory_CentralExponent_isCompact_cong
import Theorems.Thm_GlobalTheory_CentralExponent_isOpen_cong
import Theorems.Thm_GlobalTheory_SmGL_CuspMax_isCuspidal_iff_maximal
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_leviEmb_mem_normalizer
import Theorems.Thm_GlobalTheory_SmGL_nabs_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp
namespace GlobalTheory.SuperCusp
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSupercuspidal π → GlobalTheory.SmGL.IsCuspidal π := by
  intro k _ _ _ _ N V _ _ π hπ
  refine (CuspMax.isCuspidal_iff_maximal k N V π).2 ⟨hπ.1, fun r t h hr ht => ?_⟩
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun u _ => ?_)
  by_contra hu
  obtain ⟨z, hz1, hzn⟩ := CentralExponent.exists_nabs_lt_one k
  have hz : valuation k (z : k) < 1 := lt_of_le_of_ne hz1 fun h1 => by
    have := nabs_eq_one k h1
    linarith
  set A := emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin r) z, 1) with hA
  let w : ℕ → V ⧸ twKer π (unipRad k (two (stdSum h))) 1 := fun m =>
    (twKer π (unipRad k (two (stdSum h))) 1).mkQ (π (A ^ m) u)
  have hw : ∀ m, w m ≠ 0 := by
    intro m hm
    apply hu
    have hmem : π (A ^ m) u ∈ twKer π (unipRad k (two (stdSum h))) 1 :=
      (Submodule.Quotient.mk_eq_zero _).1 hm
    have hnorm : (A ^ m)⁻¹ ∈ Subgroup.normalizer ((unipRad k (two (stdSum h)) : Subgroup _) : Set _) := by
      rw [hA, ← map_pow, ← map_inv]
      exact leviEmb_mem_normalizer k (two (stdSum h)) _
    have := twKer_le_comap π _ _ hnorm hmem
    rwa [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at this
  obtain ⟨φ, hφ⟩ := exists_dual_infinite w hw
  obtain ⟨γ, hγ, hK⟩ := CentralExponent.exists_cong_subset ((hπ.1 u).mem_nhds (by simp))
  obtain ⟨l, hl, hll⟩ := exists_smooth_form_eq hπ.1 (CentralExponent.isOpen_cong γ hγ)
    (CentralExponent.isCompact_cong γ hγ) A
    (CentralExponent.cong (Fin N) γ hγ ⊓ parabLower k (two (stdSum h)) : Subgroup _)
    (fun c hc => (Subgroup.mem_inf.1 hc).1) (CentralExponent.cong_factor (stdSum h) γ hγ)
    (CentralExponent.cong_contract (stdSum h) γ hγ hz1) hK
    (φ ∘ₗ (twKer π (unipRad k (two (stdSum h))) 1).mkQ)
    (fun x hx v => congrArg φ ((Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨x, hx⟩, v, by simp⟩)))
  obtain ⟨C, hC, hsupp⟩ := hπ.2 u l hl
  exact false_of_infinite (stdSum h) ⟨0, hr⟩ ⟨0, ht⟩ hz hC hφ fun m hm => hsupp _ (by rw [hll]; exact hm)
end GlobalTheory.SuperCusp
