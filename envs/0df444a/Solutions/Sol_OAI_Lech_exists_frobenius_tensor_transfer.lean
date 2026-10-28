-- Prove2me | solution 1 for OAI.Lech.exists_frobenius_tensor_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:06:07.299117+00:00
-- url     : https://prove2.me/submissions/9d73ae41-c818-435d-9ad9-1758ebed1939

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L004
import Definitions.Def_OAIQ032L008
import Theorems.Thm_OAI_Lech_FrobeniusGrowth_frobenius_error_tendstoENNReal
import Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator
import Theorems.Thm_OAI_Lech_finite_module_tensor_asymptoticENN
import Theorems.Thm_OAI_Lech_frobeniusModule_finiteLength

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum

open TensorProduct


namespace Lech.NormalizedLength
variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

lemma map_le_annihilator_baseChange (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map (algebraMap R S) ≤ Module.annihilator S (S ⊗[R] M) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul s m =>
    rw [IsScalarTower.algebraMap_smul S r, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul, Module.mem_annihilator.mp (hI hr) m,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [smul_add, hx, hy, add_zero]

end Lech.NormalizedLength


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorGeneratorBound
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.TensorGenerator
variable {D M : Type*} [CommRing D] [AddCommGroup M] [Module D M]

variable {b : ℕ} (f : (Fin b → D) →ₗ[D] M)
  (B : Type*) [CommRing B] [Algebra D B]

lemma baseGenerators_surjective (hf : Function.Surjective f) :
    Function.Surjective (baseGenerators f B) :=
  (LinearMap.baseChange_surjective B hf).comp
    (((Pi.basisFun D (Fin b)).baseChange B).equivFun.symm.surjective)

end Lech.TensorGenerator

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusFiniteLength
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct
universe u
lemma extendScalars_annihilator {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) (I : Ideal R)
    (hI : I ≤ Module.annihilator R M) :
    I.map φ ≤ Module.annihilator S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change I.map φ ≤ Module.annihilator S (S ⊗[R] M)
  exact Lech.NormalizedLength.map_le_annihilator_baseChange I hI

lemma extendScalars_generators {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (M : ModuleCat.{u} R) {b : ℕ} (f : (Fin b → R) →ₗ[R] M)
    (hf : Function.Surjective f) :
    ∃ g : (Fin b → S) →ₗ[S] ((ModuleCat.extendScalars φ).obj M), Function.Surjective g := by
  let := φ.toAlgebra
  change ∃ g : (Fin b → S) →ₗ[S] (S ⊗[R] M), Function.Surjective g
  exact ⟨Lech.TensorGenerator.baseGenerators f S,
    Lech.TensorGenerator.baseGenerators_surjective f S hf⟩

variable (D : Type u) [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
variable (M : ModuleCat.{u} D)

lemma frobeniusModule_annihilator (I : Ideal D) (hI : I ≤ Module.annihilator D M) (n : ℕ) :
    I.map (iterateFrobenius D p n) ≤ Module.annihilator D (FrobeniusModule D p n M) :=
  extendScalars_annihilator (iterateFrobenius D p n) M I hI

lemma frobeniusModule_generators {b : ℕ} (f : (Fin b → D) →ₗ[D] M)
    (hf : Function.Surjective f) (n : ℕ) :
    ∃ g : (Fin b → D) →ₗ[D] (FrobeniusModule D p n M), Function.Surjective g :=
  extendScalars_generators (iterateFrobenius D p n) M f hf

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusTensorTransfer
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal Topology
open Filter
namespace Lech
universe u
variable (B E : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing E] [Algebra B E] [Module.Finite B E]
  (p : ℕ) [Fact p.Prime] [CharP B p]

 

theorem exists_frobenius_tensor_transfer_oai
    (hfaithful : ∀ g : B, g ≠ 0 → g • (LinearMap.id : E →ₗ[B] E) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} B), IsFiniteLength B M → ∀ a : ℝ≥0∞,
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (FrobeniusModule B p n M)).toENNReal) atTop (𝓝 a) →
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (E ⊗[B] (FrobeniusModule B p n M))).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞)*a)) := by
  obtain ⟨r,hr,h⟩ := finite_module_tensor_asymptoticENN B E hfaithful
  refine ⟨r,hr,?_⟩
  intro M hM a ha
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨I,hI,hIM⟩ := finiteLength_primary_annihilator hM
  obtain ⟨b,f,hf⟩ := Module.Finite.exists_fin' B M
  have ht := h (fun n => FrobeniusModule B p n M)
    (fun n => I.map (iterateFrobenius B p n))
    (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹) a b
    (fun n => Module.length_ne_top_iff.mpr (frobeniusModule_finiteLength B p M hM n))
    (fun n => frobeniusModule_annihilator B p M I hIM n)
    (fun n => frobeniusModule_generators B p M f hf n) ha
    (fun g hg => Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal I hI
      (mem_nonZeroDivisors_iff_ne_zero.mpr hg) p)
  apply ht.congr
  intro n
  congr 1
  exact congrArg ENat.toENNReal (TensorProduct.comm B (FrobeniusModule B p n M) E).length_eq
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.exists_frobenius_tensor_transfer_oai.{u} := @OAI.Lech.exists_frobenius_tensor_transfer_oai.{u}
