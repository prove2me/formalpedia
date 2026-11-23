-- Prove2me | solution 1 for GroundTheory.Global.cyclicHerbrand_trivial_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:19.290477+00:00
-- url     : https://prove2.me/submissions/48d3cb87-4b23-45d3-96b5-88899c3aeca7

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CyclicSubtraction
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply


attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.normHom_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {G : Type*} [Group G] [Fintype G]
namespace GroundTheory.Global
theorem _root_.solution (σ : G) :
    cyclicHerbrand (Representation.trivial ℤ G ℤ) σ = Fintype.card G := by
  set ρ := Representation.trivial ℤ G ℤ
  have hf : cycSub ρ σ = 0 := by
    ext
    simp [ρ]
  have hg : normHom ρ = (Fintype.card G : ℤ) • AddMonoidHom.id ℤ := by
    ext
    simp [ρ, normHom_apply]
  have hn : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : Nat.card (KerModRange (cycSub ρ σ) (normHom ρ)) = Fintype.card G := by
    show (normHom ρ).range.relIndex (cycSub ρ σ).ker = _
    have hr : (normHom ρ).range = AddSubgroup.zmultiples (Fintype.card G : ℤ) := by
      ext y
      simp only [hg, AddMonoidHom.mem_range, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
        AddSubgroup.mem_zmultiples_iff, smul_eq_mul]
      exact ⟨fun ⟨x, hx⟩ => ⟨x, by rw [← hx, mul_comm]⟩,
        fun ⟨x, hx⟩ => ⟨x, by rw [← hx, mul_comm]⟩⟩
    rw [hf, AddMonoidHom.ker_zero, AddSubgroup.relIndex_top_right, hr, Int.index_zmultiples,
      Int.natAbs_natCast]
  have h2 : Nat.card (KerModRange (normHom ρ) (cycSub ρ σ)) = 1 := by
    have : Subsingleton (normHom ρ).ker := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      rw [AddMonoidHom.mem_ker, hg] at ha hb
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, smul_eq_mul,
        mul_eq_zero, hn, false_or] at ha hb
      subst ha hb
      rfl
    have : Subsingleton (KerModRange (normHom ρ) (cycSub ρ σ)) := by
      constructor
      intro a b
      induction a using QuotientAddGroup.induction_on
      induction b using QuotientAddGroup.induction_on
      congr 1
      exact Subsingleton.elim _ _
    exact Nat.card_of_subsingleton 0
  rw [cyclicHerbrand, herbrandQuotient, h1, h2, Nat.cast_one, div_one]
end GroundTheory.Global
