-- Prove2me | solution 1 for LT.LatticeTree.unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6f002a39-6f01-5f52-be81-1463d08a490c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeOrbital
import Theorems.Thm_LT_LatticeTree_twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
p2m_attr_erase "simp" "LT.LatticeTree.IntegralHom.mk.sizeOf_spec LT.LatticeTree.Vertex.baseChange_mk LT.LatticeTree.vecMap_apply LT.LatticeTree.vecMap_refl LT.LatticeTree.IntegralHom.mk.injEq"

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ : GL (Fin 2) (v.adicCompletion K)) (u : (v.adicCompletionIntegers K)ˣ)
    (hdet : Matrix.det (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) u)
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
    (hSsupp : ∀ s ∈ S, s⁻¹ * γ * s ∈ AutomorphicForm.localIntegralSet K v)
    (hS :
      ∀ s ∈ S, ∀ s' ∈ S,
        ∀ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
          ∀ u ∈ AutomorphicForm.localIntegralSet K v, s' = t * s * u → s' = s)
    (hcov :
      ∀ x : GL (Fin 2) (v.adicCompletion K), x⁻¹ * γ * x ∈ AutomorphicForm.localIntegralSet K v →
        ∃ s ∈ S,
          ∃ t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))),
            ∃ u ∈ AutomorphicForm.localIntegralSet K v, x = t * s * u) :
    LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ =
      (Tc ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
          (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))) *
        ∑ s ∈ S, (St s).relIndex Tc := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
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
    LT.LatticeTree.twistedUnitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
      (v.adicCompletionIntegers K) (v.adicCompletion K)
      (LT.LatticeTree.IntegralAut.refl (v.adicCompletionIntegers K) (v.adicCompletion K)) ϖ hϖ rfl γ u hdet
      Tc (by rw [hcent]; exact hTc) St (by rw [hcent, hU]; exact hSt) S (by rw [hU]; exact hSsupp)
      (by rw [hcent, hU]; exact hS) (by rw [hcent, hU]; exact hcov)
  rw [LT.LatticeTree.twistedUnitOrbitalCount_refl, hcent] at h
  exact h

end S_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
end P2MW
export P2MW.S_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap (solution)
