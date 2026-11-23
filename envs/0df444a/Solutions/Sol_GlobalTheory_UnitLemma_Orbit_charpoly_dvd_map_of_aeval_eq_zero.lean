-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.charpoly_dvd_map_of_aeval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:17.499501+00:00
-- url     : https://prove2.me/submissions/e9ca85bf-b819-4056-b4fd-540aa4df73fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_CuspGL_irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (B : InvAlg K) (hs : B.P.Separable) (f : K.O[X]) (hf : aeval B.g f = 0) :
    B.P ∣ f.map (algebraMap K.O K.E) := by
  have h0 : aeval (LinearMap.mulLeft K.E B.g) (f.map (algebraMap K.O K.E)) = 0 := by
    have := Polynomial.aeval_algHom_apply (Algebra.lmul K.E B.A) B.g (f.map (algebraMap K.O K.E))
    rw [aeval_map_algebraMap K.E B.g f, hf, map_zero] at this
    exact this
  by_cases hz : f.map (algebraMap K.O K.E) = 0
  · rw [hz]; exact dvd_zero _
  classical
  have hP : B.P ≠ 0 := hs.ne_zero
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP hz,
    Multiset.le_iff_subset ((UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP).1 hs.squarefree)]
  intro p hp
  rw [Polynomial.mem_normalizedFactors_iff hP] at hp
  rw [Polynomial.mem_normalizedFactors_iff hz]
  exact ⟨hp.1, hp.2.1, GlobalTheory.CuspGL.irreducible_dvd_of_dvd_charpoly_of_aeval_eq_zero _ _ _ hp.1 hp.2.2 h0⟩
end GlobalTheory.UnitLemma.Orbit
