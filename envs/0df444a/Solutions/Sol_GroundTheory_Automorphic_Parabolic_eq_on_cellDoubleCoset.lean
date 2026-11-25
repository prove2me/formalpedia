-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.eq_on_cellDoubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:59:36.592671+00:00
-- url     : https://prove2.me/submissions/c29d44c7-41e8-4af1-9d4b-c7a6d92e24e2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaJacquetCell
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_mem_indSpace
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
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution {J : ℕ}
    {ψ₁ ψ₂ : levi F n γ → Representation.Coinvariants (cellRepA β γ w σ)}
    (h₁ : ψ₁ ∈ indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ))
    (h₂ : ψ₂ ∈ indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ))
    {s : levi F n γ}
    (hs : ∀ k : levi F n γ, (k : GL (Fin n) F) ∈ congruenceSubgroup F n J → ψ₁ (s * k) = ψ₂ (s * k))
    {m : levi F n γ}
    (hm : ∃ b ∈ cellLeviParabolic F β γ w, ∃ k ∈ levi F n γ ⊓ congruenceSubgroup F n J,
      (m : GL (Fin n) F) = b * s * k) : ψ₁ m = ψ₂ m := by
  obtain ⟨b, hb, k, hk, he⟩ := hm
  set bM : cellLeviSub F β γ w := ⟨⟨b, hb.1⟩, Subgroup.mem_subgroupOf.2 hb⟩
  set kM : levi F n γ := ⟨k, (Subgroup.mem_inf.1 hk).1⟩
  have hm' : m = (bM : levi F n γ) * (s * kM) := Subtype.ext (by
    rw [he]
    simp only [Subgroup.coe_mul, mul_assoc]
    rfl)
  rw [hm', ((mem_indSpace).1 h₁).1 bM, ((mem_indSpace).1 h₂).1 bM, hs kM (Subgroup.mem_inf.1 hk).2]
end GroundTheory.Automorphic.Parabolic
