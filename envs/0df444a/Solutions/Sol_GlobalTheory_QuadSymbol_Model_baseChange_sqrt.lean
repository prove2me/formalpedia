-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.Model.baseChange_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:45:02.59899+00:00
-- url     : https://prove2.me/submissions/147e42ac-c0ee-4702-94ec-4ed171f1b98a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_isQuadratic
import Theorems.Thm_GlobalTheory_QuadSymbol_Model_numberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory.QuadSymbol
open GlobalTheory GlobalTheory.QuadSymbol GlobalTheory.QuadSymbol.Model
variable {F K : Type} [Field F] [Field K] [Algebra F K] (d : F)
namespace GlobalTheory.QuadSymbol.Model
theorem _root_.solution [NumberField F] [NumberField K] [Fact (∀ r : F, r ^ 2 ≠ d + 0 * r)]
    [Fact (∀ r : K, r ^ 2 ≠ algebraMap F K d + 0 * r)] (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F (QuadraticAlgebra F d 0) K
      (QuadraticAlgebra K (algebraMap F K d) 0) (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F (QuadraticAlgebra F d 0) K
      (QuadraticAlgebra K (algebraMap F K d) 0) v.Completion := by
  have := isQuadratic d
  have := numberField d
  have := isQuadratic (algebraMap F K d)
  have := numberField (algebraMap F K d)
  letI : Algebra (QuadraticAlgebra F d 0) (QuadraticAlgebra K (algebraMap F K d) 0) :=
    (sqrtMap (K := K) d).toRingHom.toAlgebra
  have : IsScalarTower F (QuadraticAlgebra F d 0) (QuadraticAlgebra K (algebraMap F K d) 0) :=
    IsScalarTower.of_algebraMap_eq fun x => ((sqrtMap (K := K) d).commutes x).symm
  refine H.2 F _ K _ ?_
  rw [eq_top_iff]
  rintro ⟨x, y⟩ -
  rw [QuadraticAlgebra.mk_eq_add_smul_omega]
  refine add_mem (Subalgebra.algebraMap_mem _ _) (Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _)
  refine ⟨QuadraticAlgebra.omega, ?_⟩
  change sqrtMap (K := K) d _ = _
  simp [sqrtMap]
end GlobalTheory.QuadSymbol.Model
