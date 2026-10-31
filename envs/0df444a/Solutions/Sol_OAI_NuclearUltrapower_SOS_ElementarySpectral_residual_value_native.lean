-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:23:02.296523+00:00
-- url     : https://prove2.me/submissions/0baeec9b-1c8c-4992-a8f0-eac182159c8b

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_value_inv
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_value_mul
import Theorems.Thm_OAI_NuclearUltrapower_SOS_basis_good
import Theorems.Thm_OAI_NuclearUltrapower_SOS_delta_good
import Theorems.Thm_OAI_NuclearUltrapower_SOS_interpret_inv
import Theorems.Thm_OAI_NuclearUltrapower_SOS_residual_value_generic
import Theorems.Thm_OAI_NuclearUltrapower_SOS_toMatrix_inv

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegerMatrices
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower.SOS

theorem generators_det : ∀ m ∈ generators, (toMatrix m).det = 1 := by
  decide +kernel

theorem generators_inverse : ∀ m ∈ generators, matInv m ∈ generators := by
  decide +kernel

theorem genSet_inv {g : SL} (h : g ∈ genSet) : g⁻¹ ∈ genSet := by
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨matInv m, generators_inverse m hm, interpret_inv m (generators_det m hm)⟩

theorem goodWord_inv {n : ℕ} {a : Mat3} (ha : GoodWord n a) : GoodWord n (matInv a) := by
  obtain ⟨had, w, hw, hl, hs⟩ := ha
  refine ⟨by rw [toMatrix_inv, Matrix.det_adjugate, had, one_pow], w.reverse.map Inv.inv, ?_, ?_, ?_⟩
  · rw [List.map_reverse, ← List.prod_inv_reverse, hw, interpret_inv a had]
  · simpa using hl
  · intro s hmem
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
    exact genSet_inv (hs g (List.mem_reverse.mp hg))

end NuclearUltrapower.SOS
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace NuclearUltrapower.SOS
namespace ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local irreducible] gramValue eval residual

theorem residual_value_native_oai (ρ : E →* (H ≃ₗᵢ[ℂ] H)) :
    eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) residual =
      (10000000000000 : ℤ) • (eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta *
        eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta) -
      (1000000000000 : ℤ) • eval (value (A := H →L[ℂ] H) (unitaryRep ρ)) delta -
      (10 : ℤ) • gramValue (value (A := H →L[ℂ] H) (unitaryRep ρ)) := by
  apply residual_value_generic
  · intro a ha b hb
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
    exact value_mul (A := H →L[ℂ] H) (unitaryRep ρ) _ _ (delta_good hp) (delta_good hq)
  · intro a ha b hb
    rw [value_mul (A := H →L[ℂ] H) (unitaryRep ρ) _ _ (goodWord_inv (basis_good ha)) (basis_good hb),
      value_inv (A := H →L[ℂ] H) (unitaryRep ρ) _ (basis_good ha)]
end ElementarySpectral
end NuclearUltrapower.SOS
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native_oai.{u_1} := @OAI.NuclearUltrapower.SOS.ElementarySpectral.residual_value_native_oai.{u_1}
