-- Prove2me | solution 1 for MassDataIdxEmb.emb_of_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:16.091804+00:00
-- url     : https://prove2.me/submissions/61c278ee-7ec6-4175-9448-08b279ac7d08

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_QuadRoot
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_GenOfTwo
import Theorems.Thm_MassDataIdxEmb_gen_of_two
import Theorems.Thm_MassDataIdxEmb_quad_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace MassDataIdxEmb
open NumberField IsDedekindDomain Polynomial
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem finitePlace_embedding_eq_algebraMap (p : HeightOneSpectrum (𝓞 F)) (k : F) :
    FinitePlace.embedding p k = algebraMap F (p.adicCompletion F) k := rfl
private theorem norm_algebraMap_adicCompletion_lt_one_of_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∈ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ < 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_lt_one_iff_mem F p c).2 hc
private theorem norm_algebraMap_adicCompletion_eq_one_of_not_mem (p : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F)
    (hc : c ∉ p.asIdeal) : ‖algebraMap (𝓞 F) (p.adicCompletion F) c‖ = 1 := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (p.adicCompletion F), ← finitePlace_embedding_eq_algebraMap]
  exact (FinitePlace.norm_eq_one_iff_notMem F p c).2 hc
end MassDataIdxEmb
end
end

set_option autoImplicit false
noncomputable section
open MassDataIdxEmb
open NumberField IsDedekindDomain Polynomial
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace MassDataIdxEmb
theorem _root_.solution (h2 : Module.finrank F E = 2) (p : HeightOneSpectrum (𝓞 F)) (Q Q' : Ideal (𝓞 E))
    [Q.IsMaximal] [Q'.IsMaximal] (hne : Q ≠ Q') [Q.LiesOver p.asIdeal] [Q'.LiesOver p.asIdeal] :
    Nonempty (E →ₐ[F] p.adicCompletion F) := by
  obtain ⟨a, c0, c1, -, -, hP, hdeg, hc0, hc1⟩ := gen_of_two h2 p Q Q' hne
  have hint_r : IsIntegral (𝓞 F) a := Algebra.IsIntegral.isIntegral a
  have hFE : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  have hfield : minpoly F (algebraMap (𝓞 E) E a) = (minpoly (𝓞 F) a).map (algebraMap (𝓞 F) F) :=
    minpoly.isIntegrallyClosed_eq_field_fractions F E hint_r
  have hbint : IsIntegral F (algebraMap (𝓞 E) E a) := IsIntegral.of_finite F _
  have htop : IntermediateField.adjoin F {algebraMap (𝓞 E) E a} = ⊤ := by
    rw [Field.primitive_element_iff_minpoly_natDegree_eq, hfield,
      (minpoly.monic hint_r).natDegree_map, hdeg, h2]
  obtain ⟨x, hx⟩ := quad_root
    (algebraMap (𝓞 F) (p.adicCompletion F) c0) (algebraMap (𝓞 F) (p.adicCompletion F) c1)
    (norm_algebraMap_adicCompletion_eq_one_of_not_mem p c1 hc1) (norm_algebraMap_adicCompletion_lt_one_of_mem p c0 hc0)
  have hroot : aeval x (minpoly F (algebraMap (𝓞 E) E a)) = 0 := by
    rw [hfield, aeval_map_algebraMap F, hP]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    linear_combination hx
  have hpb : aeval x (minpoly F (IntermediateField.adjoin.powerBasis hbint).gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen]
    exact hroot
  let e : ↥(IntermediateField.adjoin F {algebraMap (𝓞 E) E a}) ≃ₐ[F] E :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  exact ⟨((IntermediateField.adjoin.powerBasis hbint).lift x hpb).comp e.symm.toAlgHom⟩
end MassDataIdxEmb
