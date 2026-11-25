-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.continuous_monoidHom_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:38:00.635545+00:00
-- url     : https://prove2.me/submissions/4b20deec-84a0-4933-b4bb-6947f3a7fbc4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_Abstract
import Definitions.Def_GroundTheory_GlobalFields_NormResidueSymbol_AbstractUnique
import Theorems.Thm_GroundTheory_Global_IdeleGroup_dense_localEmbeddingSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Filter Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {ψ ψ' : IdeleGroup K →* M} (hψ : Continuous ψ) (hψ' : Continuous ψ')
    (hfin : ∀ v a, ψ (finiteEmbedding v a) = ψ' (finiteEmbedding v a))
    (hinf : ∀ w a, ψ (infiniteEmbedding w a) = ψ' (infiniteEmbedding w a)) : ψ = ψ' := by
  have hle : localEmbeddingSubgroup K ≤ ψ.eqLocus ψ' :=
    sup_le (iSup_le fun v ↦ by rintro _ ⟨a, rfl⟩; exact hfin v a)
      (iSup_le fun w ↦ by rintro _ ⟨a, rfl⟩; exact hinf w a)
  exact MonoidHom.ext (congrFun (Continuous.ext_on dense_localEmbeddingSubgroup hψ hψ' fun x hx ↦ hle hx))
end GroundTheory.Global.IdeleGroup
