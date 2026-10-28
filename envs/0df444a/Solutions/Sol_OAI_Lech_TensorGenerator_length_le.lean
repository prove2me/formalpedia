-- Prove2me | solution 1 for OAI.Lech.TensorGenerator.length_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:05:21.098658+00:00
-- url     : https://prove2.me/submissions/a3327986-b4e3-41c2-b1cf-89749495883b

import Mathlib
import Definitions.Def_OAIQ032L000
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L008

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NormalizedLengthTrivialRelation
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra
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
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteTensorBound
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech.NormalizedLength.Tower
variable {R : Type*} [CommRing R] (T : Tower R)

section Bound
variable {B N : Type*} [CommRing B] [Algebra R B]
  [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

lemma length_le_quotient_mul (I : Ideal B) (hI : I ≤ Module.annihilator B N)
    {b : ℕ} (f : (Fin b → B) →ₗ[B] N) (hf : Function.Surjective f) :
    T.length N ≤ (b : ℝ≥0∞) * T.length (B ⧸ I) := by
  classical
  let P := Submodule.pi Set.univ (fun _ : Fin b => I)
  have hP : P ≤ f.ker := by
    intro x hx
    change f x = 0
    rw [pi_eq_sum_univ x, map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul]
    exact Module.mem_annihilator.mp (hI (hx i (Set.mem_univ i))) _
  let q := P.liftQ f hP
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,rfl⟩ := hf x
    exact ⟨P.mkQ y,rfl⟩
  calc
    T.length N ≤ T.length ((Fin b → B) ⧸ P) :=
      T.length_le_of_surjective (q.restrictScalars R) hq
    _ = T.length (Fin b → B ⧸ I) :=
      T.length_eq_of_equiv ((Submodule.quotientPi (fun _ : Fin b => I)).restrictScalars R)
    _ = _ := by
      suffices hlength : ∀ count : ℕ,
          T.length (Fin count → B ⧸ I) = count * T.length (B ⧸ I) from hlength b
      intro count
      induction count with
      | zero => simp [T.length_zero]
      | succ count ih =>
        rw [T.length_eq_of_equiv
          (Fin.consLinearEquiv R (fun _ : Fin (count + 1) => B ⧸ I)).symm,
          T.length_prod, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

end Bound
end Lech.NormalizedLength.Tower

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorGeneratorBound
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear
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

variable {R : Type*} [CommRing R] (T : Lech.NormalizedLength.Tower R)
  [Algebra R B]

lemma length_le_oai (hf : Function.Surjective f) (I : Ideal D)
    (hI : I ≤ Module.annihilator D M) :
    T.length (B ⊗[D] M) ≤ (b : ℝ≥0∞) * T.length (B ⧸ I.map (algebraMap D B)) := by
  exact T.length_le_quotient_mul (I.map (algebraMap D B))
    (Lech.NormalizedLength.map_le_annihilator_baseChange I hI)
    (baseGenerators f B) (baseGenerators_surjective f B hf)

end Lech.TensorGenerator

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Lech.TensorGenerator.length_le_oai.{u_1, u_2, u_3, u_4} := @OAI.Lech.TensorGenerator.length_le_oai.{u_1, u_2, u_3, u_4}
