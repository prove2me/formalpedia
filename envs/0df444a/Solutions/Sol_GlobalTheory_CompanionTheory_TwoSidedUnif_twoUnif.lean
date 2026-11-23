-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwoSidedUnif.twoUnif
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:36.800378+00:00
-- url     : https://prove2.me/submissions/eee4a69e-cdb4-4ed3-bd46-7d1f795e3d9c

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_ThetaCellCovers_VecClose
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwoUnif

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1
open scoped Pointwise Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwoSidedUnif
namespace GlobalTheory.CompanionTheory.TwoSidedUnif
theorem _root_.solution : TwoUnif := by
  intro X φ ε hφ hε
  obtain ⟨hc, hs⟩ := hφ
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have hS : IsCompact (tsupport φ) := hs
  have hK : IsCompact (N⁻¹ * tsupport φ * N⁻¹) := (hNc.inv.mul hS).mul hNc.inv
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hf : Continuous fun q : (X.G × X.G) × X.G => ‖φ (q.1.1 * q.2 * q.1.2) - φ q.2‖ := by
    have : Continuous fun q : (X.G × X.G) × X.G => q.1.1 * q.2 * q.1.2 := by fun_prop
    exact ((hc.comp this).sub (hc.comp continuous_snd)).norm
  have hev : ∀ᶠ p : X.G × X.G in 𝓝 ((1 : X.G), (1 : X.G)), ∀ y ∈ N⁻¹ * tsupport φ * N⁻¹,
      ‖φ (p.1 * y * p.2) - φ y‖ < ε := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h0 : ‖φ ((((1 : X.G), (1 : X.G)), y).1.1 * (((1 : X.G), (1 : X.G)), y).2 *
        (((1 : X.G), (1 : X.G)), y).1.2) - φ (((1 : X.G), (1 : X.G)), y).2‖ < ε := by
      simpa using hε
    exact hf.continuousAt.eventually (Iio_mem_nhds h0)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hev
  refine ⟨U ∩ V ∩ N, Filter.inter_mem (Filter.inter_mem hU hV) hN1, ?_⟩
  rintro z ⟨⟨hzU, -⟩, hzN⟩ w ⟨⟨-, hwV⟩, hwN⟩ y
  by_cases hy : y ∈ N⁻¹ * tsupport φ * N⁻¹
  · exact (hUV (Set.mk_mem_prod hzU hwV) y hy).le
  · have hy0 : φ y = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨1 * y, Set.mem_mul.2 ⟨1, ?_, y, hys, rfl⟩, 1, ?_, by simp⟩
      · simpa using h1N
      · simpa using h1N
    have hzy0 : φ (z * y * w) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hys => hy ?_
      refine Set.mem_mul.2 ⟨z⁻¹ * (z * y * w), Set.mem_mul.2 ⟨z⁻¹, ?_, z * y * w, hys, rfl⟩, w⁻¹, ?_, by group⟩
      · exact Set.inv_mem_inv.2 hzN
      · exact Set.inv_mem_inv.2 hwN
    simpa [hy0, hzy0] using hε.le
end GlobalTheory.CompanionTheory.TwoSidedUnif
