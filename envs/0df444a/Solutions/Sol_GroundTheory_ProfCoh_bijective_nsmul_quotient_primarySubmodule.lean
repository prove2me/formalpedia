-- Prove2me | solution 1 for GroundTheory.ProfCoh.bijective_nsmul_quotient_primarySubmodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:50:20.013992+00:00
-- url     : https://prove2.me/submissions/9b922ffb-a526-44d9-9c33-82015ba90205

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyCoindCokernelIso_hom
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_mem_stabilizer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.cohomologyCoindCokernelIso_hom
attribute [local simp] GroundTheory.ProfCoh.isDiscreteRep_apply
attribute [local simp] GroundTheory.ProfCoh.mem_stabilizer



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {k : Type u} [CommRing k]
omit [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (A : Rep.{u} k G)
    (hA : IsAddTorsion A) {p : ℕ} (hp : p.Prime) :
    Function.Bijective fun x : A ⧸ primarySubmodule A p => p • x := by
  set W := primarySubmodule A p
  constructor
  · have hker : ∀ x : A ⧸ W, p • x = 0 → x = 0 := by
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨k, hk⟩ := hx
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨k + 1, by rw [pow_succ, mul_smul]; exact hk⟩
    intro x y hxy
    rw [← sub_eq_zero]
    apply hker
    simp only at hxy
    rw [smul_sub, hxy, sub_self]
  · intro x
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm0, hma⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 (hA a)
    obtain ⟨e, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p hp.ne_one
    have hm'0 : m' ≠ 0 := by
      rintro rfl
      simp at hm0
    by_cases h1 : m' = 1
    · subst h1
      refine ⟨0, ?_⟩
      simp only [smul_zero]
      symm
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨e, by simpa using hma⟩
    · have hcop : Nat.Coprime p m' := (Nat.Prime.coprime_iff_not_dvd hp).2 hm'
      obtain ⟨v, -, hv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
      refine ⟨Submodule.Quotient.mk (v • a), ?_⟩
      simp only
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      refine ⟨e, ?_⟩
      obtain ⟨j, hj⟩ : ∃ j, p * v = m' * j + 1 := ⟨p * v / m', by
        have := Nat.div_add_mod (p * v) m'
        omega⟩
      have : p • v • a - a = (m' * j) • a := by
        rw [← mul_smul, hj, add_smul, one_smul, add_sub_cancel_right]
      rw [this, ← mul_smul, ← mul_assoc, mul_comm (p ^ e * m'), mul_smul, hma, smul_zero]
end GroundTheory.ProfCoh
