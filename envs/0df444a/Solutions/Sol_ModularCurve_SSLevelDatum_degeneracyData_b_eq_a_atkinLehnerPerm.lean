-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.degeneracyData_b_eq_a_atkinLehnerPerm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/4a2215ec-ed17-57bc-a935-e1d61a69c185

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm

set_option autoImplicit false

open AlgebraicCurve ModularCurve

namespace DEB2

section CurveSide

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem restrictAlong_congrEquiv (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (σ : F' ≃ₐ[K] F')
    (hσφ : (σ.symm.toAlgHom.comp φ).toRingHom.IsIntegral) (w : Place K F') :
    Place.restrictAlong φ hφ (Place.congrEquiv σ.toRingEquiv (fun c => σ.commutes c) w) =
      Place.restrictAlong (σ.symm.toAlgHom.comp φ) hσφ w := by
  apply Place.ext
  ext f
  exact Iff.rfl

end CurveSide

section Datum

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [DecidableEq K] {M s : ℕ} [NeZero M] [NeZero s]
  (X : SSLevelDatum p K M s)

omit [CharP K p] in

theorem atkinLehnerAut_symm_comp_levelAlphaC :
    X.atkinLehnerAut.symm.toAlgHom.comp (levelAlphaC K M s X.mem_M) = levelBetaC K M s X.mem_s := by
  obtain ⟨h1, h2, h3, h4⟩ := X.isAtkinLehner
  refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ({jqModC K, jqNModC K M} : Set (LaurentSeries K))) rfl ?_
  intro x hx
  rcases hx with rfl | hx
  · have e1 : levelAlphaC K M s X.mem_M ⟨jqModC K, jqModC_mem K M⟩ = jGeomGen K (M * s) :=
      Subtype.ext (coe_levelAlphaC K M s X.mem_M _)
    apply Subtype.ext
    change ((X.atkinLehnerAut.symm (levelAlphaC K M s X.mem_M ⟨jqModC K, _⟩) : modularFunctionFieldC K (M * s)) : LaurentSeries K) =
      ((levelBetaC K M s X.mem_s ⟨jqModC K, _⟩ : modularFunctionFieldC K (M * s)) : LaurentSeries K)
    rw [coe_levelBetaC, e1, ← h2, AlgEquiv.symm_apply_apply]
    rfl
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have e1 : levelAlphaC K M s X.mem_M ⟨jqNModC K M, jqNModC_mem K M⟩ = ⟨jqNModC K M, X.mem_M⟩ :=
      Subtype.ext (coe_levelAlphaC K M s X.mem_M _)
    apply Subtype.ext
    change ((X.atkinLehnerAut.symm (levelAlphaC K M s X.mem_M ⟨jqNModC K M, _⟩) : modularFunctionFieldC K (M * s)) : LaurentSeries K) =
      ((levelBetaC K M s X.mem_s ⟨jqNModC K M, _⟩ : modularFunctionFieldC K (M * s)) : LaurentSeries K)
    rw [coe_levelBetaC, e1, ← h3, AlgEquiv.symm_apply_apply]
    show jqNModC K (M * s) = qExpand K s (jqNModC K M)
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm s M]

end Datum

end DEB2

theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [DecidableEq K] (M s : ℕ) [NeZero M] [NeZero s]
    (X : SSLevelDatum p K M s) (W : ↥(ssPlaces p (M * s) K)) :
    X.degeneracyData.b W = X.degeneracyData.a (X.atkinLehnerPerm W) := by
  apply Subtype.ext
  show Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral W.1 =
    Place.restrictAlong (levelAlphaC K M s X.mem_M) X.fstIntegral (autOnPlaces K M s X.atkinLehnerAut W.1)
  have hint : (X.atkinLehnerAut.symm.toAlgHom.comp (levelAlphaC K M s X.mem_M)).toRingHom.IsIntegral := by
    rw [DEB2.atkinLehnerAut_symm_comp_levelAlphaC]; exact X.sndIntegral
  rw [autOnPlaces, DEB2.restrictAlong_congrEquiv _ _ _ hint]
  exact Place.restrictAlong_congr (DEB2.atkinLehnerAut_symm_comp_levelAlphaC X).symm _ _ _

end S_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm (solution)
