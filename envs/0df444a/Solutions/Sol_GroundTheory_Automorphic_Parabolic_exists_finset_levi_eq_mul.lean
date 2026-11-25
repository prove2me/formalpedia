-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.exists_finset_levi_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:28:57.681776+00:00
-- url     : https://prove2.me/submissions/8aeb4768-9f66-419a-8c20-454a00560470

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_levi_eq_mul
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isClosed_levi
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_relIndex_ne_zero_of_isCompact_of_isOpen
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (j : ℕ) :
    ∃ T : Finset (GL (Fin n) F), (∀ t ∈ T, t ∈ levi F n γ ⊓ integralGL F n) ∧
      ∀ m ∈ levi F n γ, ∃ b ∈ cellLeviParabolic F β γ w, ∃ t ∈ T,
        ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n j, m = b * t * k := by
  classical
  set K₀ := levi F n γ ⊓ integralGL F n
  set L := (levi F n γ ⊓ congruenceSubgroup F n j).subgroupOf K₀
  have hK₀ : IsCompact (K₀ : Set (GL (Fin n) F)) :=
    (isCompact_integralGL F n).inter_left isClosed_levi
  have hfin : L.index ≠ 0 := by
    have h := relIndex_ne_zero_of_isCompact_of_isOpen hK₀ (isOpen_congruenceSubgroup F n j)
    have : L = (congruenceSubgroup F n j).subgroupOf K₀ := by
      ext x
      simp only [L, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨x.2.1, h⟩⟩
    rw [this]
    exact h
  have : L.FiniteIndex := ⟨hfin⟩
  let _ := Fintype.ofFinite (K₀ ⧸ L)
  refine ⟨Finset.univ.image fun q : K₀ ⧸ L => ((Quotient.out q : K₀) : GL (Fin n) F),
    fun t ht => ?_, fun m hm => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    exact (Quotient.out q).2
  · obtain ⟨b, hb, k, hk, rfl⟩ := exists_levi_eq_mul (β := β) (w := w) hm
    set q : K₀ ⧸ L := QuotientGroup.mk ⟨k, hk⟩
    have hq : (Quotient.out q : K₀)⁻¹ * ⟨k, hk⟩ ∈ L := by
      rw [← QuotientGroup.eq]
      exact QuotientGroup.out_eq' q
    refine ⟨b, hb, (Quotient.out q : K₀), Finset.mem_image_of_mem _ (Finset.mem_univ q),
      ((Quotient.out q : K₀) : GL (Fin n) F)⁻¹ * k, Subgroup.mem_subgroupOf.1 hq, ?_⟩
    group
end GroundTheory.Automorphic.Parabolic
