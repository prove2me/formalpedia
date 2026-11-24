-- Prove2me | solution 1 for GlobalTheory.PrimeToNormalVanishing.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:31:04.631713+00:00
-- url     : https://prove2.me/submissions/f6a8590a-f9d5-46de-8316-bba82e63b567

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PrimeToNormalVanishing
namespace GlobalTheory.PrimeToNormalVanishing
theorem _root_.solution {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [TopologicalSpace M]
    [DiscreteTopology M] (F : Γ × Γ × Γ → M) (hF : Continuous F) :
    ∃ U : OpenNormalSubgroup Γ, ∃ F' : Γ ⧸ U.toSubgroup → Γ ⧸ U.toSubgroup → Γ ⧸ U.toSubgroup → M,
      ∀ a b c : Γ, F' a b c = F (a, b, c) := by
  have h1 : ∀ᶠ u in nhds (1 : Γ × Γ × Γ), ∀ x ∈ (Set.univ : Set (Γ × Γ × Γ)), F (x * u) = F x := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun x _ => ?_
    have ho : IsOpen {z : (Γ × Γ × Γ) × (Γ × Γ × Γ) | F (z.2 * z.1) = F z.2} :=
      (isOpen_discrete {p : M × M | p.1 = p.2}).preimage
        (f := fun z : (Γ × Γ × Γ) × (Γ × Γ × Γ) => (F (z.2 * z.1), F z.2)) (by fun_prop)
    exact ho.mem_nhds (by simp)
  obtain ⟨A, hA, BC, hBC, h2⟩ := mem_nhds_prod_iff.1 h1
  obtain ⟨B, hB, C, hC, h3⟩ := mem_nhds_prod_iff.1 hBC
  obtain ⟨W, hW, hWo, hW1⟩ := mem_nhds_iff.1 (Filter.inter_mem hA (Filter.inter_mem hB hC))
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWo hW1
  refine ⟨U, fun a b c => F (a.out, b.out, c.out), fun a b c => ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup a
  obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup b
  obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul U.toSubgroup c
  simp only [hu, hv, hw]
  exact h2 (a := ((u : Γ), (v : Γ), (w : Γ))) ⟨(hW (hU u.2)).1,
    h3 ⟨(hW (hU v.2)).2.1, (hW (hU w.2)).2.2⟩⟩ (a, b, c) trivial
end GlobalTheory.PrimeToNormalVanishing
