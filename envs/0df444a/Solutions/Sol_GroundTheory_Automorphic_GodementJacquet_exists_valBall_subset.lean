-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.exists_valBall_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:37.730071+00:00
-- url     : https://prove2.me/submissions/2c929c3b-e7b0-48c0-bef1-f9518387ba92

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleFiniteLength
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {S : Set (Matrix (Fin n) (Fin n) F)}
    (hS : S ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) F)) :
    ∃ r : ℕ, {Y : Matrix (Fin n) (Fin n) F | ∀ i j, Y i j ∈ LocalField.valBall F r} ⊆ S := by
  classical
  have hS' : S ∈ Filter.pi fun _ : Fin n => 𝓝 (0 : Fin n → F) := by
    rw [← nhds_pi]; exact hS
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 hS'
  have ht' : ∀ i, t i ∈ Filter.pi fun _ : Fin n => 𝓝 (0 : F) := fun i => by
    rw [← nhds_pi]; exact ht i
  choose J u hu hJu using fun i => Filter.mem_pi'.1 (ht' i)
  have hr : ∀ i j, ∃ r : ℤ, (LocalField.valBall F r : Set F) ⊆ u i j := fun i j => by
    obtain ⟨r, -, hr⟩ := LocalField.hasBasis_nhds_zero_valBall.mem_iff.1 (hu i j)
    exact ⟨r, hr⟩
  choose r hr using hr
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => (r p.1 p.2).toNat, fun Y hY => hIt ?_⟩
  intro i _
  refine hJu i ?_
  intro j _
  refine hr i j (LocalField.valBall_antitone ?_ (hY i j))
  have : (r i j).toNat ≤ Finset.univ.sup fun p : Fin n × Fin n => (r p.1 p.2).toNat :=
    Finset.le_sup (f := fun p : Fin n × Fin n => (r p.1 p.2).toNat) (Finset.mem_univ (i, j))
  omega
end GroundTheory.Automorphic.GodementJacquet
