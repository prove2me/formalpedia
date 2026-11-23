-- Prove2me | solution 1 for GlobalTheory.covolume_lattice_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:18.701637+00:00
-- url     : https://prove2.me/submissions/2a8d1802-39e7-4aad-9f38-f4f5ff21fdfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    ZLattice.covolume L.lattice = ‖a‖ ^ 2 * τ.im := by
  let L' : PeriodPair := ⟨a * τ, a, by
    rw [LinearIndependent.pair_iff]
    intro s t e
    have e2 : (s * τ + t : ℂ) = 0 := mul_left_cancel₀ ha (by
      simp only [Complex.real_smul] at e
      linear_combination e)
    have e3 : s = 0 := by simpa [τ.im_ne_zero] using congrArg Complex.im e2
    exact ⟨e3, by simpa [e3] using e2⟩⟩
  have e : L.lattice = L'.lattice := by
    ext x
    simp only [h, PeriodPair.mem_lattice, L']
    exact exists₂_congr fun m n => by rw [show a * (m * τ + n) = m * (a * τ) + n * a by ring]
  have hy := τ.im_pos
  rw [e, ZLattice.covolume_eq_det_mul_measureReal _ _ L'.latticeBasis
    Complex.orthonormalBasisOneI.toBasis,
    MeasureTheory.measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _),
    MeasureTheory.Measure.real, OrthonormalBasis.coe_toBasis,
    Complex.orthonormalBasisOneI.volume_parallelepiped, ENNReal.toReal_one, mul_one,
    ← abs_of_nonneg (show 0 ≤ ‖a‖ ^ 2 * τ.im by positivity), ← abs_neg (_ * _)]
  congr 1
  rw [Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, L', Complex.sq_norm, Complex.normSq_apply]
  ring
end GlobalTheory
