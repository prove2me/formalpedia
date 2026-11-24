-- Prove2me | solution 1 for GlobalTheory.ideal_eq_bot_of_forall_prime_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:00:08.461359+00:00
-- url     : https://prove2.me/submissions/e0dbc96e-526a-4237-a920-6b0daf3e90b9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsumSmulEqOneOfTame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulMemSpanInvariantsSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SubalgebraEqTopOfForallPrimeSmulMemSup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantTowerAlgebraMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {B T : Type} [CommRing B] [CommRing T]
    [Algebra B T] (J : Ideal T) (hJ : J.FG)
    (h : ∀ q : Ideal B, q.IsPrime → ∀ x ∈ J, ∃ s : B, s ∉ q ∧
      s • x ∈ q • (J.restrictScalars B)) : J = ⊥ := by
  by_cases hJt : Submodule.annihilator J = ⊤
  · exact Submodule.annihilator_eq_top_iff.1 hJt
  obtain ⟨n, hn, hJn⟩ := Ideal.exists_le_maximal _ hJt
  have hle : J ≤ n • J := by
    intro x hxJ
    obtain ⟨s, hs, hx⟩ := h (n.comap (algebraMap B T)) (Ideal.comap_isPrime _ _) x hxJ
    have hx' : s • x ∈ n • J := by
      refine Submodule.smul_induction_on hx ?_ ?_
      · intro r hr c hc
        rw [← algebraMap_smul T r c]
        exact Submodule.smul_mem_smul hr hc
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb
    obtain ⟨t, m, hm, e⟩ := hn.exists_inv (x := algebraMap B T s) hs
    have e' : x = t • (s • x) + m • x := by
      rw [← algebraMap_smul T s x, ← mul_smul, ← add_smul, e, one_smul]
    rw [e']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx') (Submodule.smul_mem_smul hm hxJ)
  obtain ⟨r, hr, hrM⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul n J hJ hle
  have hrJ : r ∈ n := hJn (Submodule.mem_annihilator.2 hrM)
  exfalso
  apply hn.ne_top
  rw [Ideal.eq_top_iff_one]
  have := n.sub_mem hrJ hr
  rwa [sub_sub_cancel] at this
end GlobalTheory
