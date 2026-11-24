-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Casselman.exists_mem_inf_conj_of_isDom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:55.57484+00:00
-- url     : https://prove2.me/submissions/1ad3ad58-f172-402d-bf73-f491d6e6ed3c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IwahoriFactorisation_StrictDominance_JointGeneralisedEigenvectors_IsJointGenEig
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsMemInfConjOfIsDom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep PositivityTheory.SphericalProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Casselman
namespace GlobalTheory.CompanionTheory.Casselman
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : PositivityTheory.SphericalProduct.CassData G), ∀ t : D.T, D.IsDom t → ∀ y ∈ D.J,
      ∃ a ∈ D.J ⊓ D.N, a⁻¹ * y ∈ D.J ⊓ D.J.map (MulAut.conj (t : G)).toMonoidHom := by
  intro G _ _ _ D t ht y hy
  obtain ⟨c, hc, b, hb, a, ha, rfl⟩ := D.fact_up y hy
  have hb' : b ∈ D.J := (Subgroup.mem_inf.1 hb).1
  have ha' : a ∈ D.J := (Subgroup.mem_inf.1 ha).1
  have hbt : (t : G)⁻¹ * b * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.2 b hb).2).1
  have hat : (t : G)⁻¹ * a * t ∈ D.J := (Subgroup.mem_inf.1 (ht.2.1 a ha)).1
  have he : c⁻¹ * (c * b * a) = b * a := by group
  refine ⟨c, hc, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
  · rw [he]
    exact D.J.mul_mem hb' ha'
  · rw [he, Subgroup.mem_map]
    refine ⟨((t : G)⁻¹ * b * t) * ((t : G)⁻¹ * a * t), D.J.mul_mem hbt hat, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
end GlobalTheory.CompanionTheory.Casselman
