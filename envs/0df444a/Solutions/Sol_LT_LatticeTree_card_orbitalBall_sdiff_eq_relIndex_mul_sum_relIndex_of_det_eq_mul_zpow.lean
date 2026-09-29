-- Prove2me | solution 1 for LT.LatticeTree.card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8b3aa386-7c4b-52e5-8c12-90cf4a628f5c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeBaseChange
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ϖ : v.adicCompletionIntegers K) (hϖ : Irreducible ϖ) (γ : GL (Fin 2) (v.adicCompletion K))
    (b : ℤ) (n : ℕ) (hn : 1 ≤ n) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u *
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (2 * b + (n : ℤ)))
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal
        ![algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ (b + (n : ℤ)),
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ^ b])
    (Tc : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hTc : ∀ t : GL (Fin 2) (v.adicCompletion K),
      t ∈ Tc ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        ∃ w : (v.adicCompletionIntegers K)ˣ,
          Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
            algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w)
    (St : GL (Fin 2) (v.adicCompletion K) → Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hSt : ∀ s t : GL (Fin 2) (v.adicCompletion K),
      t ∈ St s ↔ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        s⁻¹ * t * s ∈ AutomorphicForm.localIntegralSet K v)
    (S : Finset (GL (Fin 2) (v.adicCompletion K)))
    (hSsupp : ∀ s ∈ S,
      s⁻¹ * γ * s ∈
        AutomorphicForm.localIntegralSet K v *
            ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
          AutomorphicForm.localIntegralSet K v)
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K),
        x⁻¹ * γ * x ∈
          AutomorphicForm.localIntegralSet K v *
              ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
            AutomorphicForm.localIntegralSet K v →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) n γ \
          LT.LatticeTree.orbitalBall (R := v.adicCompletionIntegers K)
            (LT.LatticeTree.unitOfNeZero (K := v.adicCompletion K) hϖ.ne_zero) (n - 1) γ) =
      (Tc ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S, (St s).relIndex Tc := by
  haveI : Finite ((v.adicCompletionIntegers K) ⧸ Ideal.span {ϖ}) := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    exact inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  have hcent : AutomorphicForm.sigmaCentralizer
      (LT.LatticeTree.IntegralAut.refl (v.adicCompletionIntegers K) (v.adicCompletion K)).mapGL γ =
        Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) := by
    have hid : (LT.LatticeTree.IntegralAut.refl (v.adicCompletionIntegers K) (v.adicCompletion K)).mapGL =
        MonoidHom.id (GL (Fin 2) (v.adicCompletion K)) :=
      MonoidHom.ext fun g => LT.LatticeTree.IntegralAut.mapGL_refl g
    rw [hid, AutomorphicForm.sigmaCentralizer_id]
  have hrange : Set.range (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      first
        | exact a.2
        | simpa using a.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hU :
      AutomorphicForm.integralUnitsSet (Set.range (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))) =
        AutomorphicForm.localIntegralSet K v := by
    rw [hrange]
    rfl
  have h :=
    LT.LatticeTree.card_twistedOrbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
      (v.adicCompletionIntegers K) (v.adicCompletion K)
      (LT.LatticeTree.IntegralAut.refl (v.adicCompletionIntegers K) (v.adicCompletion K)) ϖ hϖ rfl γ b n hn u hdet
      dl hdl
      Tc (by rw [hcent]; exact hTc) St (by rw [hcent, hU]; exact hSt) S (by rw [hU]; exact hSsupp)
      (by rw [hcent, hU]; exact hS) (by rw [hcent, hU]; exact hcov)
  simp only [LT.LatticeTree.twistedOrbitalBall_refl] at h
  rw [hcent] at h
  exact h

end S_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow
end P2MW
export P2MW.S_LT_LatticeTree_card_orbitalBall_sdiff_eq_relIndex_mul_sum_relIndex_of_det_eq_mul_zpow (solution)
