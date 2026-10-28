-- Prove2me | solution 1 for OAI.Lech.CharP.perfection_complex_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:59:14.982679+00:00
-- url     : https://prove2.me/submissions/65589dc7-8af7-4511-ad7f-da5ea47b6b9b

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_CharP_dutta_limit_from_perfection
import Theorems.Thm_OAI_Lech_CharP_normalized_perfection_module_finite
import Theorems.Thm_OAI_Lech_frobenius_shortComplex_homology_finiteLength

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct

lemma finite_extendScalars {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat R) [Module.Finite R M] :
    Module.Finite S ((ModuleCat.extendScalars f).obj M) := by
  let := f.toAlgebra
  change Module.Finite S (S ⊗[R] M)
  infer_instance


instance finite_frobeniusModule (D : Type*) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (n : ℕ) (M : ModuleCat D) [Module.Finite D M] :
    Module.Finite D (FrobeniusModule D p n M) :=
  finite_extendScalars (iterateFrobenius D p n) M
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma free_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.Free S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Free S (S ⊗[R] M)
  infer_instance

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaEulerLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
lemma frobenius_weight_eq (p d n : ℕ) :
    (p:ℝ)^(-(n*d:ℤ)) = (((p:ℝ)^n)^d)⁻¹ := by
  rw [← Nat.cast_mul,zpow_neg,zpow_natCast,pow_mul]

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaMultiplicity_eq_of_tendsto (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (L : ℝ)
    (hL : Tendsto (duttaSequence R p F) atTop (𝓝 L)) :
    duttaMultiplicity R p F = L := hL.limUnder_eq
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaFrobeniusShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p]

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaSequence_frobenius (F : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℕ) :
    duttaSequence R p (frobeniusComplex R p n F) m =
      ((p:ℝ)^n)^dimension R * duttaSequence R p F (n+m) := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : shortEuler R (frobeniusComplex R p m (frobeniusComplex R p n F)) =
      shortEuler R (frobeniusComplex R p (n+m) F) := by
    apply Finset.sum_congr rfl
    intro j _
    have H := ((homologyFunctor (ModuleCat R) (.up ℤ) (-(j:ℤ))).mapIso
      (frobeniusComplexAddIso p F n m)).toLinearEquiv.length_eq
    change Module.length R ((frobeniusComplex R p m (frobeniusComplex R p n F)).homology (-(j:ℤ))) =
      Module.length R ((frobeniusComplex R p (n+m) F).homology (-(j:ℤ))) at H
    rw [H]
  unfold duttaSequence
  rw [he,frobenius_weight_eq,frobenius_weight_eq,pow_add,mul_pow]
  field_simp

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaLimit_frobenius (F : CochainComplex (ModuleCat.{u} R) ℤ) (L : ℝ)
    (hL : Tendsto (duttaSequence R p F) atTop (𝓝 L)) (n : ℕ) :
    Tendsto (duttaSequence R p (frobeniusComplex R p n F)) atTop
      (𝓝 (((p:ℝ)^n)^dimension R*L)) := by
  have ht : Tendsto (fun m : ℕ => n+m) atTop atTop := by
    simpa only [Nat.add_comm n] using tendsto_add_atTop_nat n
  have H := (hL.comp ht).const_mul (((p:ℝ)^n)^dimension R)
  apply H.congr
  intro m
  exact (duttaSequence_frobenius p F n m).symm

lemma frobenius_finiteHomology (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (n : ℕ) :
    IsFiniteHomologyComplex R (frobeniusComplex R p n F) := by
  refine ⟨fun i => ?_,fun i => ?_,fun i hi => ?_,fun i => ?_⟩
  · let := hF.term_free i
    exact free_extendScalars (iterateFrobenius R p n) (F.X i)
  · let := hF.term_finite i
    exact finite_extendScalars (iterateFrobenius R p n) (F.X i)
  · exact (ModuleCat.extendScalars (iterateFrobenius R p n)).map_isZero (hF.bounded i hi)
  · exact frobenius_shortComplex_homology_finiteLength p F hF n i
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaPerfectionValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (IsLocalRing.ResidueField D) p]

lemma perfection_complex_value_oai (ell : AllModuleLength (PerfectClosure D p))
    (hlim : ∀ (M : ModuleCat.{u} D),IsFiniteLength D M →
      Tendsto (fun n : ℕ => ((p:ℝ≥0∞)^(n*dimension D))⁻¹*
        (Module.length D (FrobeniusModule D p n M)).toENNReal) atTop
        (𝓝 (ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M))))
    (hparam : ∀ (z : Fin (dimension D) → D),
      (Ideal.span (Set.range z)).radical = IsLocalRing.maximalIdeal D →
      ∀ a : ℕ,0<a → ell.value (ModuleCat.of (PerfectClosure D p)
        ((PerfectClosure D p) ⧸ (parameterIdeal D z a).map (PerfectClosure.of D p))) =
        (a:ℝ≥0∞)^dimension D*ENNReal.ofReal (Primary.multiplicity (Ideal.span (Set.range z))))
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) (n : ℕ) :
    (ell.value ((((ModuleCat.extendScalars (PerfectClosure.of D p)).mapHomologicalComplex _).obj
      (frobeniusComplex D p n F)).homology 0)).toReal =
        ((p:ℝ)^n)^dimension D*duttaMultiplicity D p F := by
  have H (G : CochainComplex (ModuleCat.{u} D) ℤ) (hG : IsFiniteHomologyComplex D G) :=
    dutta_limit_from_perfection D p G hG ell
      (normalized_perfection_module_finite D p ell hparam (G.homology 0) (hG.homology_finite_length 0))
      (hlim (G.homology 0) (hG.homology_finite_length 0))
  have hFval := duttaMultiplicity_eq_of_tendsto p F _ (H F hF)
  have hshift := duttaLimit_frobenius p F _ (H F hF) n
  rw [← hFval] at hshift
  exact tendsto_nhds_unique (H (frobeniusComplex D p n F) (frobenius_finiteHomology p F hF n)) hshift
end Lech.CharP

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.CharP.perfection_complex_value_oai.{u} := @OAI.Lech.CharP.perfection_complex_value_oai.{u}
