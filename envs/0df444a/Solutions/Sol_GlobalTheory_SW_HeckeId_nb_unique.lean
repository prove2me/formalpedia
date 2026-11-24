-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.nb_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:27:40.927306+00:00
-- url     : https://prove2.me/submissions/9de04118-6157-4efe-a8bb-bd5e400755e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_eq_of_le
import Theorems.Thm_GlobalTheory_SW_HeckeId_inf_mem_hyp
import Theorems.Thm_GlobalTheory_SW_Nbr_SD_eq_of_le
import Theorems.Thm_GlobalTheory_SW_Nbr_eq_nbOf
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


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
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ Λ' Λ'' : Lt E n}
    (h : Λ ∈ Vset E n M) (h' : Λ' ∈ Nb M P Λ) (h'' : Λ'' ∈ Nb M P Λ) {y : Fin n → E} (hy : y ∉ Λ)
    (hy' : y ∈ Λ') (hy'' : y ∈ Λ'') : Λ' = Λ'' := by
  have := max_of_norm hP.1 hP.2.2.1
  have hS : SD Λ := h.2.1
  have key : ∀ L ∈ Nb M P Λ, y ∈ L → L.comap Λ.subtype = perp Λ y := fun L hL hyL =>
    Hyp.eq_of_le (inf_mem_hyp hP hL) (fun x hx => (hL.1.2.1 _).1 hx y hyL)
      fun H => hy ((hS y).2 fun z hz => Int'.symm (H ⟨z, hz⟩))
  have e' := congrArg (Submodule.map Λ.subtype) ((key _ h' hy').trans (key _ h'' hy'').symm)
  simp only [Submodule.map_comap_subtype] at e'
  exact (eq_nbOf hP h h').trans (e' ▸ (eq_nbOf hP h h'').symm)
end GlobalTheory.SW.HeckeId
