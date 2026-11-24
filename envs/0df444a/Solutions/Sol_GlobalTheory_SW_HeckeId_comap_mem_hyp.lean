-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.comap_mem_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:26:09.151895+00:00
-- url     : https://prove2.me/submissions/b00efc55-084f-4147-bee0-0ef7c73730d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_inf_mem_hyp
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_nb_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' : Lt E n}
    (h : Λ ∈ Vset E n M) (h' : Λ' ∈ Nb M P Λ) (u : X →ₗ[𝓞 E] (Fin n → E)) (hu : ¬ ∀ ξ, u ξ ∈ Λ)
    (hu' : ∀ ξ, u ξ ∈ Λ') : Λ.comap u ∈ Hyp (conjI P) X := by
  obtain ⟨f, -, hf⟩ := inf_mem_hyp (good_conj hP) (nb_symm hP h h')
  have hk : LinearMap.ker (f ∘ₗ u.codRestrict Λ' hu') = Λ.comap u := by
    rw [LinearMap.ker_comp, hf]; rfl
  refine ⟨_, fun h0 => hu fun ξ => ?_, hk⟩
  have : ξ ∈ Λ.comap u := by rw [← hk, h0]; trivial
  exact this
end GlobalTheory.SW.HeckeId
