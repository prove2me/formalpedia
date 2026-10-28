-- Prove2me | solution 1 for OAI.Lech.TensorIdeal.fibreMap_kernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:15:17.347393+00:00
-- url     : https://prove2.me/submissions/6cbedcf9-fa1e-483a-8e66-29fbf5e19e6b

import Mathlib
import Definitions.Def_OAIQ032L023

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech

section


universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]


variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma eq_of_iso {M N : ModuleCat.{u} R} (e : M ≅ N)
    (hM : powerTorsion I M) (hN : powerTorsion I N) : ℓ.value M = ℓ.value N :=
  le_antisymm (ℓ.le_of_mono e.hom hN) (ℓ.le_of_mono e.inv hM)

end TorsionLength
end


universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma value_linearEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R M) = ℓ.value (ModuleCat.of R N) := by
  let e' := e.toModuleIso
  exact ℓ.eq_of_iso e' ((powerTorsion I).prop_of_iso e'.symm hN) hN

end TorsionLength
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionZeroStability
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum TensorProduct
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}


namespace TorsionLength
variable (ell : TorsionLength I)

lemma zero_of_surjective_torsion {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hT : powerTorsion I (ModuleCat.of R M)) (hM : ell.value (ModuleCat.of R M)=0) :
    ell.value (ModuleCat.of R N)=0 := by
  let : Epi (ModuleCat.ofHom f) := (ModuleCat.epi_iff_surjective _).mpr hf
  exact le_antisymm ((ell.le_of_epi (ModuleCat.ofHom f) hT).trans_eq hM) bot_le



lemma iSup_zero_torsion (hds : ell.DirectSumZero) {ι M : Type u}
    [AddCommGroup M] [Module R M] (U : ι → Submodule R M)
    (hT : powerTorsion I (ModuleCat.of R M))
    (hU : ∀ i, ell.value (ModuleCat.of R (U i))=0) :
    ell.value (ModuleCat.of R (⨆ i,U i : Submodule R M))=0 := by
  classical
  obtain ⟨a,ha⟩ := hT
  have hUa : ∀ i, I^a ≤ Module.annihilator R (U i) := fun i =>
    ha.trans ((U i).subtype.annihilator_le_of_injective (U i).injective_subtype)
  have hsum : powerTorsion I (ModuleCat.of R (⨁ i,U i)) := by
    refine ⟨a,?_⟩
    change I^a ≤ Module.annihilator R (Π₀ i, U i)
    rw [Module.annihilator_dfinsupp]
    exact le_iInf hUa
  have hh := ell.zero_of_surjective_torsion (DirectSum.coeLinearMap U).rangeRestrict
    (DirectSum.coeLinearMap U).surjective_rangeRestrict hsum (hds (fun i => U i) a hUa hU)
  rwa [DirectSum.range_coeLinearMap] at hh

lemma zero_of_ranges_torsion (hds : ell.DirectSumZero) {ι M : Type u}
    [AddCommGroup M] [Module R M] {N : ι → Type u}
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (f : ∀ i,N i →ₗ[R] M)
    (hT : powerTorsion I (ModuleCat.of R M))
    (hNT : ∀ i,powerTorsion I (ModuleCat.of R (N i)))
    (hN : ∀ i,ell.value (ModuleCat.of R (N i))=0)
    (hspan : (⨆ i,(f i).range)=⊤) : ell.value (ModuleCat.of R M)=0 := by
  have hh := ell.iSup_zero_torsion hds (fun i => (f i).range) hT
    (fun i => ell.zero_of_surjective_torsion (f i).rangeRestrict
      (f i).surjective_rangeRestrict (hNT i) (hN i))
  rw [hspan,ell.value_linearEquiv (Submodule.topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M) hT] at hh
  exact hh

end TorsionLength
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionChartKernel
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
lemma powerTorsion_submodule {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hT : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R N) := by
  obtain ⟨a,ha⟩ := hT
  exact ⟨a,ha.trans (N.subtype.annihilator_le_of_injective N.injective_subtype)⟩
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TorsionTensorLeft
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TorsionLength
open CategoryTheory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)
  {A M N : Type u} [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]

omit [Module R N] [IsScalarTower R A N] in
lemma tensor_torsion_left (hT : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (M ⊗[A] N)) := by
  obtain ⟨a,ha⟩ := hT
  refine ⟨a,?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  induction x using OAI.tensorInductionOn with
  | tmul m n =>
      rw [TensorProduct.smul_tmul',Module.mem_annihilator.mp (ha hr) m,TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add,hx,hy,add_zero]

omit [Module R N] [IsScalarTower R A N] in
lemma tensor_zero_left_torsion (hds : ell.DirectSumZero)
    (hT : powerTorsion I (ModuleCat.of R M)) (hM : ell.value (ModuleCat.of R M)=0) :
    ell.value (ModuleCat.of R (M ⊗[A] N))=0 := by
  let f (n : N) : M →ₗ[R] M ⊗[A] N := ((TensorProduct.mk A M N).flip n).restrictScalars R
  apply ell.zero_of_ranges_torsion hds f (tensor_torsion_left hT) (fun _ => hT) (fun _ => hM)
  apply top_unique
  intro x _
  induction x using OAI.tensorInductionOn with
  | tmul m n => exact (le_iSup (fun n => (f n).range) n) ⟨m,rfl⟩
  | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)

omit [Module R N] [IsScalarTower R A N] in
lemma rTensor_map_kernel_zero_torsion (hds : ell.DirectSumZero)
    {V : Type u} [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]
    (f : M →ₗ[A] N) (hf : Function.Surjective f)
    (hTk : powerTorsion I (ModuleCat.of R f.ker))
    (hker : ell.value (ModuleCat.of R f.ker)=0) :
    ell.value (ModuleCat.of R (f.rTensor V).ker)=0 := by
  let k := f.ker.subtype.rTensor V
  have he := _root_.rTensor_exact V f.exact_subtype_ker_map hf
  let q : f.ker ⊗[A] V →ₗ[R] (f.rTensor V).ker :=
    (k.restrictScalars R).codRestrict ((f.rTensor V).ker.restrictScalars R) (fun x => by
      change (f.rTensor V) (k x)=0
      exact he.apply_apply_eq_zero x)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨v,hv⟩ := he x.val |>.mp x.property
    exact ⟨v,Subtype.ext hv⟩
  exact ell.zero_of_surjective_torsion q hq (tensor_torsion_left hTk)
    (ell.tensor_zero_left_torsion hds hTk hker)
end Lech.TorsionLength

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FibreSquare
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
open scoped TensorProduct
universe u

section Square
variable {R A B C D : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
  [AddCommGroup C] [Module A C] [Module R C] [IsScalarTower R A C]
  [AddCommGroup D] [Module A D] [Module R D] [IsScalarTower R A D]
  (I : Ideal R) (a : A →ₗ[A] C) (b : B →ₗ[A] D) (g : C →ₗ[A] D)
  (ha : Function.Surjective a) (hb : Function.Surjective b)
  (hka : (a.restrictScalars R).ker = I • (⊤ : Submodule R A))
  (hkb : (b.restrictScalars R).ker = I • (⊤ : Submodule R B))
  (hsq : b 1=g (a 1))
  (V : Type u) [AddCommGroup V] [Module A V] [Module R V] [IsScalarTower R A V]

include ha hb hka hkb hsq in
lemma fibreMap_kernel_zero_oai (ell : TorsionLength I) (hds : ell.DirectSumZero)
    (hg : Function.Surjective g) (hTc : powerTorsion I (ModuleCat.of R C))
    (hkg : ell.value (ModuleCat.of R g.ker)=0) :
    ell.value (ModuleCat.of R (fibreMap I (A:=A) (B:=B) V).ker)=0 := by
  have ht := TorsionLength.tensor_torsion_left (A:=A) (N:=V) hTc
  have htk := powerTorsion_submodule I ((g.rTensor V).ker.restrictScalars R) ht
  have he := ell.value_linearEquiv (fibreKernelEquiv I a b g ha hb hka hkb hsq V) htk
  exact he.trans (ell.rTensor_map_kernel_zero_torsion hds g hg
    (powerTorsion_submodule I (g.ker.restrictScalars R) hTc) hkg)

end Square
end Lech.TensorIdeal

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.TensorIdeal.fibreMap_kernel_zero_oai.{u} := @OAI.Lech.TensorIdeal.fibreMap_kernel_zero_oai.{u}
