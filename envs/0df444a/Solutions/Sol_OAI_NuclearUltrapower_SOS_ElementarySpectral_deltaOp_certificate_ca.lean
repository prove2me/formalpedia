-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:05:45.843294+00:00
-- url     : https://prove2.me/submissions/42671c26-3515-4b42-b6b4-3ea814f01966

import Mathlib
import Definitions.Def_OAIQ229C036
import Definitions.Def_OAIQ229C037
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_value_inv_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_value_mul_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_basis_good_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_delta_good_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_eval_mul_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_goodWord_inv_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_gramData_roots_ca
import Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_eval_ca

section
-- module Solutions.Q229_CA.NuclearUltrapower_SOSSemantics
attribute [-instance] _root_.OAI.NuclearUltrapower.strongDualInner
attribute [-simp] _root_.OAI.CoarseAssembly.adjoint_apply_isometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
variable {α A : Type*} [DecidableEq α]

section EvalOperations
variable [Ring A]
omit [DecidableEq α] in
theorem eval_scale (f : α → A) (ps : Poly α) (k : ℤ) :
    eval f (ps.map (fun p => (p.1, k*p.2))) = k • eval f ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, eval_cons, smul_add, ih, mul_smul]

end EvalOperations
end NuclearUltrapower.SOS

end

end OAI
end

section
-- module Solutions.Q229_CA.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.CoarseAssembly.baseUnionDecidableEq _root_.OAI.CoarseAssembly.instFintypeFiberVertex _root_.OAI.CoarseAssembly.vertexUnionDecidableEq _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS
open NuclearUltrapower.SL3Certificate

theorem residualRows_decomp : residualRows = residualRow0 :: residualRow1 ::
    (basis.zip gramData).map (fun p => gramPolyRow p.1 p.2) := by rfl

section Operator
variable {A : Type*} [Ring A] [StarRing A]

theorem eval_gram_rows (f : Mat3 → A)
    (hf : ∀ a ∈ basis, ∀ b ∈ basis,
      f (matMul (matInv a) b) = star (f a) * f b) :
    eval f ((basis.zip gramData).flatMap (fun p => gramPolyRow p.1 p.2)) =
      (-10 : ℤ) • gramValue f := by
  rw [gramData_roots_ca]
  simp only [List.zip_map_right, List.flatMap_map, Prod.map, id_eq,
    Function.comp_def, gramPolyRow, List.map_map]
  rw [eval_flatMap]
  have hrow (p : Mat3 × List ℤ) (hp : p ∈ rootPairs) :
      eval f ((basis.zip columns).map (fun q =>
        (matMul (matInv p.1) q.1, -10 * dot p.2 q.2))) =
        (-10 : ℤ) • (rootPairs.map (fun q => dot p.2 q.2 • (star (f p.1) * f q.1))).sum := by
    simp only [eval, List.map_map, Function.comp_def, mul_smul, List.smul_sum,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro q hq
    rw [hf p.1 (List.of_mem_zip hp).1 q.1 (List.of_mem_zip hq).1]
  change (rootPairs.map (fun p => eval f ((basis.zip columns).map
    (fun q => (matMul (matInv p.1) q.1, -10 * dot p.2 q.2))))).sum = _
  rw [List.map_congr_left hrow]
  simp only [gramValue, List.smul_sum, List.map_map, Function.comp_def]

end Operator
end NuclearUltrapower.SOS
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem operator_certificate (D Q R : H →L[ℂ] H)
    (h : R = (10000000000000 : ℤ) • (D*D) - (1000000000000 : ℤ) • D - (10 : ℤ) • Q) :
    (10000000000000 : ℝ) • (D*D) - (1000000000000 : ℝ) • D = (10 : ℤ) • Q + R := by
  rw [h]
  ext x
  simp only [add_apply, sub_apply, smul_apply]
  rw [← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
    ← Int.cast_smul_eq_zsmul ℝ]
  norm_num only [Int.cast_ofNat]
  abel

theorem residualInE_operator (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    SOSEnergy.polyOperator ρ residualInE =
      eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual := by
  simp only [SOSEnergy.polyOperator, residualInE, eval, List.map_map, Function.comp_def,
    value, unitaryRep_coe]

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

section
noncomputable section
namespace NuclearUltrapower.SOS
section
variable {A : Type*} [Ring A] [StarRing A]
theorem residual_value_generic (f : Mat3 → A)
    (hf : ∀ a ∈ delta.map Prod.fst, ∀ b ∈ delta.map Prod.fst,
      f (matMul a b) = f a * f b)
    (hg : ∀ a ∈ basis, ∀ b ∈ basis,
      f (matMul (matInv a) b) = star (f a) * f b) :
    eval f residual = (10000000000000 : ℤ) • (eval f delta * eval f delta) -
      (1000000000000 : ℤ) • eval f delta - (10 : ℤ) • gramValue f := by
  rw [residual_eval_ca, residualRows_decomp]
  simp only [List.flatten_cons, eval_append]
  rw [residualRow0, eval_scale, residualRow1, eval_scale]
  have hm : eval f (polyMul delta delta) = eval f delta * eval f delta := by
    apply eval_mul_ca
    intro p hp q hq
    exact hf p.1 (List.mem_map_of_mem hp) q.1 (List.mem_map_of_mem hq)
  rw [hm]
  rw [← List.flatMap_def, eval_gram_rows f hg]
  simp only [neg_smul, sub_eq_add_neg]
  rw [add_assoc]
end
namespace ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local irreducible] gramValue eval residual

theorem residual_value_native (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual =
      (10000000000000 : ℤ) • (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta *
        eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta) -
      (1000000000000 : ℤ) • eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta -
      (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ)) := by
  apply residual_value_generic
  · intro a ha b hb
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
    exact value_mul_ca (A := H →L[ℂ] H) (unitaryRep ρ) _ _ (delta_good_ca hp) (delta_good_ca hq)
  · intro a ha b hb
    rw [value_mul_ca (A := H →L[ℂ] H) (unitaryRep ρ) _ _ (goodWord_inv_ca (basis_good_ca ha)) (basis_good_ca hb),
      value_inv_ca (A := H →L[ℂ] H) (unitaryRep ρ) _ (basis_good_ca ha)]
end ElementarySpectral
end NuclearUltrapower.SOS
end
end

section

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace NuclearUltrapower.SOS.ElementarySpectral
section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local irreducible] gramValue eval residual

theorem deltaOp_certificate_ca_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    (10000000000000 : ℝ) • (deltaOp ρ * deltaOp ρ) - (1000000000000 : ℝ) • deltaOp ρ =
      gramOp ρ + SOSEnergy.polyOperator ρ residualInE := by
  rw [residualInE_operator]
  exact operator_certificate
    (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta)
    (gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ)))
    (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual)
    (residual_value_native ρ)

end Hilbert
end NuclearUltrapower.SOS.ElementarySpectral
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.deltaOp_certificate_ca_oai.{u_1}
