-- Prove2me | solution 2 for MasulloGRH.nuclear_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:03:08.248648+00:00
-- url     : https://prove2.me/submissions/e1853ce3-0565-4d0b-b2d0-a484043d191a

import Theorems.Thm_MasulloGRH_nuclear_of_separated_quotient

set_option autoImplicit false

namespace MasulloGRH.NQAux

open scoped ComplexOrder

universe u

theorem quot_lc (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›) (V : Submodule ℂ E) :
    IsLocallyConvexTopology (E ⧸ V) inferInstance := by
  obtain ⟨ι, hι, p, hp⟩ := hE
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  have : ContinuousSMul ℝ E := ⟨by
    have := (continuous_smul (M := ℂ) (X := E)).comp
      (Complex.continuous_ofReal.prodMap continuous_id)
    refine this.congr fun x => ?_
    simp [Function.comp, Complex.coe_smul]⟩
  have : LocallyConvexSpace ℝ E := hp.toLocallyConvexSpace
  have : ContinuousSMul ℝ (E ⧸ V) := ⟨by
    have := (continuous_smul (M := ℂ) (X := E ⧸ V)).comp
      (Complex.continuous_ofReal.prodMap continuous_id)
    refine this.congr fun x => ?_
    simp [Function.comp, Complex.coe_smul]⟩
  have : LocallyConvexSpace ℝ (E ⧸ V) := by
    have hb := (LocallyConvexSpace.convex_basis_zero (𝕜 := ℝ) (E := E)).map V.mkQ
    rw [(Submodule.isOpenQuotientMap_mkQ V).map_nhds_eq, map_zero] at hb
    refine LocallyConvexSpace.ofBasisZero ℝ (E ⧸ V) _ _ hb ?_
    rintro s ⟨-, hs⟩
    exact hs.linear_image (V.mkQ.restrictScalars ℝ)
  have : LocallyConvexSpace ℂ (E ⧸ V) := by
    refine LocallyConvexSpace.ofBasisZero ℂ (E ⧸ V) _ _
      (LocallyConvexSpace.convex_basis_zero (𝕜 := ℝ) (E := E ⧸ V)) ?_
    rintro s ⟨-, hs⟩
    exact convex_of_nonneg_surjective_algebraMap _
      (fun z hz => by
        obtain ⟨x, hx, rfl⟩ := RCLike.nonneg_iff_exists_ofReal.mp (Set.mem_Ici.mp hz)
        exact ⟨x, hx, rfl⟩) hs
  have : PolynormableSpace ℂ (E ⧸ V) := LocallyConvexSpace.toPolynormableSpace
  exact ⟨_, ⟨⟨0, continuous_const⟩⟩, _, PolynormableSpace.withSeminorms ℂ (E ⧸ V)⟩

end MasulloGRH.NQAux

open MasulloGRH MasulloGRH.NQAux

namespace MasulloGRH
open TensorProduct Topology
universe u
end MasulloGRH

open TensorProduct Topology

universe u

theorem solution (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : MasulloGRH.IsNuclear E) (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    MasulloGRH.IsNuclear (E ⧸ V) := by
  have hlc := hE.1.1
  have hq := quot_lc E hlc V
  obtain ⟨ι, hι, p, hp⟩ := hlc
  have := hp.topologicalAddGroup
  have : IsClosed (V : Set E) := hV
  refine nuclear_of_separated_quotient E (E ⧸ V) hE ⟨hq, inferInstance⟩ V.mkQ V.mkQ_surjective ?_
  apply le_antisymm
  · refine le_sInf ?_
    rintro t ⟨-, ht⟩
    have h2 : TopologicalSpace.coinduced (V.mkQ : E → E ⧸ V) inferInstance ≤ t :=
      continuous_iff_coinduced_le.mp ht
    exact h2
  · exact sInf_le ⟨hq, Submodule.continuous_mkQ V⟩
