-- Prove2me | solution 1 for GlobalTheory.DetBound.exists_wedge_eq_smul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:10:56.364387+00:00
-- url     : https://prove2.me/submissions/b28e3b30-7a53-474e-bf52-285f937c5ac9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
namespace GlobalTheory.DetBound
theorem _root_.solution {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] {n : ℕ} (hn : Module.finrank O M = n) (v : Fin n → M) (D : O)
    (hD : ∀ x : M, D • x ∈ Submodule.span O (Set.range v)) (ω : ⋀[O]^n M) (hω : O ∙ ω = ⊤) :
    ∃ u : O, exteriorPower.ιMulti O n v = u • ω ∧ u ∣ D ^ n := by
  let b := Module.finBasisOfFinrankEq O M hn
  let L := exteriorPower.alternatingMapLinearEquiv b.det
  have hL : ∀ w, L (exteriorPower.ιMulti O n w) = b.det w := fun w =>
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (hω ▸ Submodule.mem_top : exteriorPower.ιMulti O n v ∈ O ∙ ω)
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.1 (hω ▸ Submodule.mem_top : exteriorPower.ιMulti O n b ∈ O ∙ ω)
  have hu' : b.det v = u * L ω := by rw [← hL, ← hu, map_smul, smul_eq_mul]
  let A : M →ₗ[O] M := b.constr O v
  have hA : ∀ j, A (b j) = v j := fun j => b.constr_basis O v j
  have hAv : b.det v = LinearMap.det A := by
    have : (A ∘ b) = v := funext hA
    rw [← this, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  have hrange : ∀ j, ∃ y, A y = D • b j := by
    intro j
    have h := hD (b j)
    rw [← b.constr_range O (f := v)] at h
    exact h
  choose y hy using hrange
  let B' : M →ₗ[O] M := b.constr O y
  have hAB : A ∘ₗ B' = D • LinearMap.id := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, B', b.constr_basis, hy, LinearMap.smul_apply, LinearMap.id_apply]
  have hdet : LinearMap.det A * LinearMap.det B' = D ^ n := by
    rw [← LinearMap.det_comp, hAB, LinearMap.det_smul, LinearMap.det_id, mul_one, hn]
  refine ⟨u, hu.symm, ⟨L ω * LinearMap.det B', ?_⟩⟩
  rw [← hdet, ← hAv, hu', mul_assoc]
end GlobalTheory.DetBound
