-- Prove2me | solution 1 for GroundTheory.ProfCoh.exists_finite_stable_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:47:42.074845+00:00
-- url     : https://prove2.me/submissions/082989b1-aa30-4815-9089-fc6270bc72a3

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_cohomologyCoindCokernelIso_hom
import Theorems.Thm_GroundTheory_ProfCoh_isDiscreteRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_isOpen_stabilizer
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
namespace GroundTheory.ProfCoh
theorem _root_.solution [CompactSpace G] (A : Rep.{u} (ULift.{u} ℤ) G)
    [IsDiscreteRep A] {p : ℕ} (hp : 0 < p) (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) (a : A) :
    ∃ W : Submodule (ULift.{u} ℤ) A, (∀ g, W ≤ W.comap (A.ρ g)) ∧ Finite W ∧ a ∈ W := by
  let O : Set A := Set.range fun g : G => A.ρ g a
  have hO : O.Finite := by
    have := Subgroup.quotient_finite_of_isOpen _ (isOpen_stabilizer A a)
    refine (Set.finite_range fun q : G ⧸ stabilizer A.ρ a => A.ρ q.out a).subset ?_
    rintro _ ⟨g, rfl⟩
    obtain ⟨s, hgs⟩ := QuotientGroup.mk_out_eq_mul (stabilizer A.ρ a) g
    refine ⟨(g : G ⧸ stabilizer A.ρ a), ?_⟩
    simp only [hgs, map_mul, Module.End.mul_apply]
    rw [(mem_stabilizer _ _ _).1 s.2]
  refine ⟨Submodule.span _ O, fun g => Submodule.span_le.2 ?_, ?_, Submodule.subset_span ⟨1, by simp⟩⟩
  · rintro _ ⟨h, rfl⟩
    show A.ρ g (A.ρ h a) ∈ Submodule.span _ O
    exact Submodule.subset_span ⟨g * h, by simp [map_mul, Module.End.mul_apply]⟩
  · have hsub : (Submodule.span (ULift.{u} ℤ) O : Set A) ⊆ AddSubgroup.closure O := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact AddSubgroup.subset_closure hx
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul r x _ hx =>
        rw [SetLike.mem_coe, show r = ((r.down : ℤ) : ULift.{u} ℤ) by ext; simp,
          Int.cast_smul_eq_zsmul]
        exact zsmul_mem hx r.down
    have : Finite O := hO.to_subtype
    have : Finite (AddSubgroup.closure O) := AddCommGroup.finite_of_fg_isAddTorsion (G := AddSubgroup.closure O) fun x => by
      obtain ⟨k, hk⟩ := hA x
      exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨p ^ k, pow_pos hp k, Subtype.ext hk⟩
    exact ((Set.toFinite (AddSubgroup.closure O : Set A)).subset hsub).to_subtype
end GroundTheory.ProfCoh
