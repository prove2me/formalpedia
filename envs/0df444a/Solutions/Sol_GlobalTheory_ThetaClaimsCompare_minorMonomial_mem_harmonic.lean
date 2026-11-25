-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.minorMonomial_mem_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:00:57.126937+00:00
-- url     : https://prove2.me/submissions/c56d7af5-43aa-4089-9b82-98f3bc79827d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
import Theorems.Thm_GlobalTheory_minorHarm_pderiv_comm
import Theorems.Thm_GlobalTheory_minorHarm_pderiv_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (col : ∀ σ, Fin (r σ) → Fin n)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution (cc : T → T) (isX : T → Prop)
    (hdis : ∀ τ, isX τ → ∀ i j, col τ i ≠ col (cc τ) j) (a : T → ℕ → ℕ) :
    minorsP r n col k a ∈ harmK r n k cc isX (fun _ => 1) := by
  classical
  let S : Set (Letter T r n) := {v | ∃ j, col v.1 j = v.2.2}
  have hS : minorsP r n col k a ∈ MvPolynomial.supported k S := by
    refine Subalgebra.prod_mem _ fun t _ => Subalgebra.prod_mem _ fun s _ => Subalgebra.pow_mem _ ?_ _
    rw [minor, Matrix.det_apply']
    refine Subalgebra.sum_mem _ fun g _ => Subalgebra.mul_mem _ (intCast_mem _ _)
      (Subalgebra.prod_mem _ fun a _ => ?_)
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
  intro τ hτ i i'
  simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, Derivation.coeFn_coe]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hbb : b = b'
  · subst hbb
    by_cases hb : ∃ j, col (cc τ) j = b
    · obtain ⟨j', hj'⟩ := hb
      rw [minorHarm_pderiv_comm, minorHarm_pderiv_eq_zero hS, map_zero, smul_zero]
      rintro ⟨j, hj⟩
      exact hdis τ hτ j j' (hj.trans hj'.symm)
    · rw [minorHarm_pderiv_eq_zero hS (v := ⟨cc τ, i', b⟩) hb, map_zero, smul_zero]
  · rw [Matrix.one_apply_ne hbb, zero_smul]
end GlobalTheory.ThetaClaimsCompare
