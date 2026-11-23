-- Prove2me | solution 1 for GlobalTheory.FibreLinInd.exists_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:04.199817+00:00
-- url     : https://prove2.me/submissions/154a0ef0-f8e8-48b0-b452-130ebd685a99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsOpenSetOfLinearIndependentOnFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.FibreLinInd
namespace GlobalTheory.FibreLinInd
theorem _root_.solution {K A : Type} [Field K] {r : ℕ} (v : A → Fin r → K)
    (h : ∀ c : Fin r → K, (∀ a, ∑ i, c i * v a i = 0) → c = 0) :
    ∃ a : Fin r → A, (Matrix.of fun k i => v (a k) i).det ≠ 0 := by
  classical
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hφ0
    have hφ' : ∀ w : Fin r → K, φ w = ∑ i, φ (Pi.single i 1) * w i := fun w => by
      rw [LinearMap.pi_apply_eq_sum_univ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
      congr 2
      ext j
      simp [Pi.single_apply, eq_comm]
    have := h (fun i => φ (Pi.single i 1)) fun a => by
      rw [← hφ']
      exact hφ (Submodule.subset_span ⟨a, rfl⟩)
    refine LinearMap.ext fun w => ?_
    rw [hφ']
    simp [congrFun this]
  obtain ⟨κ, a, -, hs, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Fin r → K) := Module.Basis.mk hli (by rw [hs, hspan])
  let e : κ ≃ Fin r := b.indexEquiv (Pi.basisFun K (Fin r))
  refine ⟨a ∘ e.symm, ?_⟩
  have h2 : LinearIndependent K ((v ∘ a) ∘ e.symm) := hli.comp _ e.symm.injective
  have h3 : IsUnit (Matrix.of fun k i => v ((a ∘ e.symm) k) i) :=
    Matrix.linearIndependent_rows_iff_isUnit.1 h2
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h3).ne_zero
end GlobalTheory.FibreLinInd
