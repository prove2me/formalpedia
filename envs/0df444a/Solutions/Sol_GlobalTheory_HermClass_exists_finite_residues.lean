-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_finite_residues
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:32.759795+00:00
-- url     : https://prove2.me/submissions/d5bce90c-9da4-479a-ae62-344221637f63

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
namespace GlobalTheory.HermClass
theorem _root_.solution {V : Type} [AddCommGroup V] (L : Submodule ℤ V) (hL : L.FG)
    {m : ℤ} (hm : m ≠ 0) :
    ∃ R : Set V, R.Finite ∧ (∀ ρ ∈ R, ρ ∈ L) ∧ ∀ x ∈ L, ∃ ρ ∈ R, ∃ y ∈ L, x = ρ + m • y := by
  have : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL
  let P : Submodule ℤ L := LinearMap.range (m • LinearMap.id)
  have : Finite (L ⧸ P) := Module.finite_of_fg_torsion _ fun q => by
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    refine ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, ?_⟩
    change m • P.mkQ x = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  choose s hs using P.mkQ_surjective
  refine ⟨Set.range fun q => (s q : V), Set.finite_range _, ?_, fun x hx => ?_⟩
  · rintro _ ⟨q, rfl⟩; exact (s q).2
  · have h := hs (P.mkQ ⟨x, hx⟩)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.eq] at h
    obtain ⟨y, hy⟩ := h
    refine ⟨_, ⟨P.mkQ ⟨x, hx⟩, rfl⟩, y, y.2, ?_⟩
    have := congrArg Subtype.val hy
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul_of_tower,
      Submodule.coe_sub] at this
    rw [this]; simp
end GlobalTheory.HermClass
