-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_adicCompletion_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:05.763818+00:00
-- url     : https://prove2.me/submissions/16cc2934-b6b9-454f-bc08-1c3a2674c62b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Galois
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_UnramifiedNorms
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq_of_mulEquiv
import Theorems.Thm_GroundTheory_Global_mem_zpowers_mulEquiv
import Theorems.Thm_GroundTheory_Global_ofMulDistribMulAction_decomposition_units
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_cycHerbrand_units_eq_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel GroundTheory.GroupCoh
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
namespace GroundTheory.Global
theorem _root_.solution [Fintype (MulAction.stabilizer Gal(L/K) w.asIdeal)]
    (τ : MulAction.stabilizer Gal(L/K) w.asIdeal) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
          (w.adicCompletion L)ˣ) τ =
        Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  obtain ⟨h1, h2⟩ := cycHerbrand_eq_of_mulEquiv
    (ρ' := Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w.asIdeal)
      (w.adicCompletion L)ˣ)
    (ρ := Representation.ofMulDistribMulAction Gal(w.adicCompletion L/v.adicCompletion K)
      (w.adicCompletion L)ˣ)
    (decompositionMulEquiv v w) (AddEquiv.refl _)
    (fun σ x ↦ ofMulDistribMulAction_decomposition_units v w σ x) τ
  obtain ⟨h3, h4⟩ := GroundTheory.LocalField.cycHerbrand_units_eq_finrank
    (K := v.adicCompletion K) (L := w.adicCompletion L)
    (mem_zpowers_mulEquiv (decompositionMulEquiv v w) hτ)
  exact ⟨h1.2 h3, h2.trans h4⟩
end GroundTheory.Global
