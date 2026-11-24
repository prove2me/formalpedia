-- Prove2me | solution 1 for GlobalTheory.ShortVectors.exists_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:48:10.631865+00:00
-- url     : https://prove2.me/submissions/4daef61e-5ddd-4c6d-84fe-4936c6963895

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
open GlobalTheory.ShortVectors
variable {V : Type} [AddCommGroup V] [Module ℚ V]
namespace GlobalTheory.ShortVectors
theorem _root_.solution {M : ℕ} [FiniteDimensional ℚ V] (hM : finrank ℚ V = M)
    (B : LinearMap.BilinForm ℚ V) (hs : B.IsSymm) (hp : ∀ x, 0 ≤ B x x) :
    ∃ φ : V →ₗ[ℚ] EuclideanSpace ℝ (Fin M), ∀ x y, inner ℝ (φ x) (φ y) = (B x y : ℝ) := by
  classical
  let _ : Invertible (2 : ℚ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hs)
  let e : Fin M ≃ Fin (finrank ℚ V) := finCongr hM.symm
  let c : Fin M → ℝ := fun i => Real.sqrt (B (v (e i)) (v (e i)))
  let F : V → Fin M → ℝ := fun x i => c i * (v.repr x (e i) : ℝ)
  let φ : V →ₗ[ℚ] EuclideanSpace ℝ (Fin M) :=
    { toFun := fun x => (EuclideanSpace.equiv (Fin M) ℝ).symm (F x)
      map_add' := fun x y => by
        ext i
        simp [F, mul_add]
      map_smul' := fun q x => by
        ext i
        simp [F, Rat.smul_def, mul_left_comm] }
  refine ⟨φ, fun x y => ?_⟩
  have hB : B x y = ∑ j, v.repr x j * v.repr y j * B (v j) (v j) := by
    conv_lhs => rw [← v.sum_repr x, ← v.sum_repr y]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · ring
    · intro k _ hk
      have h0 : B (v k) (v j) = 0 := hv hk
      simp [h0]
    · simp
  have hinner : inner ℝ (φ x) (φ y) = ∑ i, c i ^ 2 * ((v.repr x (e i) : ℝ) * (v.repr y (e i) : ℝ)) := by
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [F]
    ring
  rw [hinner, hB, Rat.cast_sum]
  refine Fintype.sum_equiv e _ _ fun i => ?_
  simp only [c, Rat.cast_mul]
  rw [Real.sq_sqrt (Rat.cast_nonneg.mpr (hp _))]
  ring
end GlobalTheory.ShortVectors
