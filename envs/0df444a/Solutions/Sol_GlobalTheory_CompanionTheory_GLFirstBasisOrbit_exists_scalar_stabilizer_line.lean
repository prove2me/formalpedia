-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_scalar_stabilizer_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:23.89175+00:00
-- url     : https://prove2.me/submissions/2f3445e8-40be-402c-9e89-725ac76cdcf5

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_smul_mem_gmap
import Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_first_basis_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLFirstBasisOrbit
variable {k : Type} [Field k] {n : ℕ}
namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit
theorem _root_.solution (g : GL (Fin (n + 1)) k)
    (h : gmap g (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n}) :
    ∃ s : k, s ≠ 0 ∧ g.val *ᵥ e0 k n = s • e0 k n := by
  have h1 : g.val *ᵥ e0 k n ∈ Submodule.span k {e0 k n} := by
    rw [← h, smul_mem_gmap]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h1
  refine ⟨s, ?_, hs.symm⟩
  rintro rfl
  have h2 : g.val *ᵥ e0 k n = 0 := by rw [← hs, zero_smul]
  have h3 := congrArg (fun z => (g⁻¹).val *ᵥ z) h2
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h3
  exact first_basis_ne_zero h3
end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
