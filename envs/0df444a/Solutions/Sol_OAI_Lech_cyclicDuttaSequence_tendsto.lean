-- Prove2me | solution 1 for OAI.Lech.cyclicDuttaSequence_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:17:32.052712+00:00
-- url     : https://prove2.me/submissions/d2749e53-9bb5-4cef-8b1d-1d66d88a084f

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_CharP_dutta_limit_from_perfection
import Theorems.Thm_OAI_Lech_CharP_exists_length_with_module_limit
import Theorems.Thm_OAI_Lech_CharP_normalized_perfection_module_finite
import Theorems.Thm_OAI_Lech_cyclicDuttaSequence_small
import Theorems.Thm_OAI_Lech_dutta_dimension_zero
import Theorems.Thm_OAI_Lech_finiteHomology_extendScalars

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
namespace Lech.RootTower
open scoped ENNReal TensorProduct
variable {A D : Type*} [CommRing A] [CommRing D] [IsLocalRing A] [IsLocalRing D]
  [Algebra A D] [IsLocalHom (algebraMap A D)]

lemma length_eq_of_residue_surjective
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField D)))
    (M : Type*) [AddCommGroup M] [Module A M] [Module D M] [IsScalarTower A D M] :
    Module.length A M = Module.length D M := by
  rw [IsLocalRing.length_restrictScalars A D M,
    Module.length_eq_of_surjective (R := IsLocalRing.ResidueField D) hres]
  simp

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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
open scoped TensorProduct nonZeroDivisors

open scoped nonZeroDivisors


namespace Lech



theorem dimension_cast (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] : (dimension A : WithBot ℕ∞) = ringKrullDim A := by
  have hb := ringKrullDim_ne_bot (R := A)
  have ht := ringKrullDim_ne_top (R := A)
  unfold dimension
  generalize he : ringKrullDim A = d at *
  cases d with
  | bot => exact (hb rfl).elim
  | coe d =>
    simp only [WithBot.unbotD_coe]
    exact congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞))
      (ENat.natCast_toNat (fun h => ht (by simp [h])))



end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CompleteQuotient
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open IsLocalRing
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
lemma finite_module_isAdicComplete (I : Ideal R) [IsAdicComplete I R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  apply (AdicCompletion.of_bijective_iff (I:=I) (M:=M)).mp
  let e := (TensorProduct.lid R M).symm.trans
    (TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M))
  let e' := (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M).restrictScalars R
  have he : ∀ x : M, e' (e x)=AdicCompletion.of I M x := by
    intro x
    change AdicCompletion.ofTensorProduct I M
      ((AdicCompletion.of I R 1) ⊗ₜ[R] x)=_
    rw [AdicCompletion.ofTensorProduct_tmul]
    change (1 : AdicCompletion I R) • AdicCompletion.of I M x=_
    rw [one_smul]
  have hb := e'.bijective.comp e.bijective
  simpa only [Function.comp_def,he] using hb

lemma prime_quotient_complete [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (P : Ideal R) [P.IsPrime] [IsLocalRing (R ⧸ P)] :
    IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) := by
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have := finite_module_isAdicComplete (maximalIdeal R) (R ⧸ P)
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective]
  exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) (R ⧸ P)).mpr inferInstance
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaData
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]


omit [IsNoetherianRing R] [IsLocalRing R] in
lemma IsShortComplex.finiteHomology [IsNoetherianRing R] [IsLocalRing R]
    {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (hF : IsShortComplex R F) : IsFiniteHomologyComplex R F :=
  ⟨hF.term_free,hF.term_finite,hF.bounded,hF.homology_finite_length⟩


end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ZeroHomologyScalarExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

variable [IsNoetherianRing R] [IsLocalRing R]
omit [IsNoetherianRing R] [IsLocalRing R] in
lemma IsFiniteHomologyComplex.d_zero_one_eq_zero
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsFiniteHomologyComplex R F) :
    F.d 0 1 = 0 :=
  (hF.bounded 1 (Or.inr (by omega))).eq_of_tgt _ _
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
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionComplexCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
lemma restriction_homology_length
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)))
    (F : CochainComplex (ModuleCat.{u} S) ℤ) (i : ℤ) :
    Module.length R
      ((((ModuleCat.restrictScalars (algebraMap R S)).mapHomologicalComplex _).obj F).homology i) =
      Module.length S (F.homology i) := by
  rw [(restrictionHomologyIso (algebraMap R S) F i).toLinearEquiv.length_eq]
  let M := (ModuleCat.restrictScalars (algebraMap R S)).obj (F.homology i)
  let : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul (fun r x => rfl)
  exact RootTower.length_eq_of_residue_surjective hres M

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaPerfectResidue
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

lemma exists_dutta_limit (hh : 0 < dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F) :
    Tendsto (duttaSequence D p F) atTop (𝓝 (duttaMultiplicity D p F)) := by
  obtain ⟨ell,hlim,hcyc,hparam,hK,hpos⟩ := exists_length_with_module_limit D p hh
  have hfinite := normalized_perfection_module_finite D p ell hparam (F.homology 0)
    (hF.homology_finite_length 0)
  have hl := dutta_limit_from_perfection D p F hF ell hfinite
    (hlim (F.homology 0) (hF.homology_finite_length 0))
  rw [duttaMultiplicity_eq_of_tendsto p F _ hl]
  exact hl
end Lech.CharP

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimeFiltrationSupport
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Lech.PrimeFiltration
open Filter IsLocalRing
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

attribute [local instance] OAI.Lech.PrimeFiltration.quotient_local
omit [IsNoetherianRing R] in
lemma primary_quotient (I p : Ideal R) [p.IsPrime] (hI : I.radical = maximalIdeal R) :
    (I.map (Ideal.Quotient.mk p)).radical = maximalIdeal (R ⧸ p) := by
  let : IsLocalHom (Ideal.Quotient.mk p) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  apply le_antisymm
  · apply (maximalIdeal.isMaximal _).isPrime.radical_le_iff.mpr
    exact (Ideal.map_mono (Ideal.le_radical.trans hI.le)).trans
      (map_maximalIdeal_le (Ideal.Quotient.mk p))
  · rw [←map_maximalIdeal_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective]
    rw [←hI]
    exact Ideal.map_radical_le (Ideal.Quotient.mk p)

lemma quotient_dimension_le (p : Ideal R) (hp : p.IsPrime) :
    Lech.dimension (R ⧸ p) ≤ Lech.dimension R := by
  let : p.IsPrime := hp
  apply (Nat.cast_le (α := WithBot ℕ∞)).mp
  rw [Lech.dimension_cast,Lech.dimension_cast]
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

end Lech.PrimeFiltration

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_QuotientShort
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex IsLocalRing
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

attribute [local instance] OAI.Lech.quotient_local
lemma isAlgClosed_quotient_residue [IsAlgClosed (ResidueField R)] (P : Ideal R) [P.IsPrime] :
    IsAlgClosed (ResidueField (R ⧸ P)) :=
  IsAlgClosed.of_ringEquiv (ResidueField R) (ResidueField (R ⧸ P)) (quotientResidueEquiv P)

omit [IsNoetherianRing R] in
lemma quotient_tensor_subsingleton [IsNoetherianRing R] (P : Ideal R) [P.IsPrime]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : Subsingleton (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).obj M))) :
    Subsingleton M := by
  let φ := Ideal.Quotient.mk P
  let := φ.toAlgebra
  have he := TensorProduct.quotTensorEquivQuotSMul M P
  let : Subsingleton ((R ⧸ P) ⊗[R] M) := h
  have hz : Subsingleton (M ⧸ P • (⊤ : Submodule R M)) :=
    he.toEquiv.surjective.subsingleton
  have htop := Submodule.Quotient.subsingleton_iff.mp hz
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot P (⊤ : Submodule R M)
    Module.Finite.fg_top htop.ge
    ((le_maximalIdeal (show P ≠ ⊤ from Ideal.IsPrime.ne_top inferInstance)).trans
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]))
  have hzero : ∀ x : M,x=0 := by
    intro x
    exact (Submodule.mem_bot R).mp (hbot ▸ (Submodule.mem_top : x ∈ (⊤:Submodule R M)))
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

lemma shortComplex_quotient (P : Ideal R) [P.IsPrime]
    (hd : dimension (R ⧸ P)=dimension R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    IsShortComplex (R ⧸ P)
      (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F) := by
  have hh := finiteHomology_extendScalars (Ideal.Quotient.mk P) hd
    (PrimeFiltration.primary_quotient (maximalIdeal R) P (Ideal.IsPrime.radical inferInstance))
    F hF.finiteHomology
  refine ⟨hh.term_free,hh.term_finite,hh.bounded,hh.homology_finite_length,?_⟩
  intro hz
  have e := scalarExtensionZeroHomologyIso (Ideal.Quotient.mk P) F
    hF.finiteHomology.d_zero_one_eq_zero
  have hz' := ModuleCat.isZero_iff_subsingleton.mp (hz.of_iso e.symm)
  have : IsNoetherian R (F.homology 0) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hF.homology_finite_length 0)).1
  exact hF.homology_zero_nonzero (ModuleCat.isZero_iff_subsingleton.mpr
    (quotient_tensor_subsingleton P (F.homology 0) hz'))
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CyclicDutta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
attribute [local instance] quotient_local quotient_localHom
local instance duttaResidueCharP (A : Type u) [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p] : CharP (ResidueField A) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have h := congrArg (residue A) (CharP.cast_eq_zero A p)
    simpa only [map_natCast,map_zero] using h)
local instance duttaQuotientAlgebraLocal (P : Ideal R) [P.IsPrime] :
    IsLocalHom (algebraMap R (R ⧸ P)) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

lemma tensor_quotient_homology_length (P : Ideal R) [P.IsPrime]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module.length R (((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))).homology i)=
      Module.length (R ⧸ P)
        ((((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F).homology i) := by
  rw [(homologyMapIso (tensorScalarExtensionIso (S:=R ⧸ P) F) i).toLinearEquiv.length_eq]
  exact restriction_homology_length (quotient_residue_surjective P) _ i

attribute [local instance] OAI.Lech.duttaQuotientCharP
lemma cyclicDuttaSequence_full (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (P : Ideal R) [P.IsPrime]
    (hd : dimension (R ⧸ P)=dimension R) (n : ℕ) :
    cyclicDuttaSequence p F P n=duttaSequence (R ⧸ P) p
      (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F) n := by
  unfold cyclicDuttaSequence duttaSequence shortEuler
  rw [hd]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [tensor_quotient_homology_length]
  rw [(homologyMapIso (frobeniusBaseChangeIso p (Ideal.Quotient.mk P) F n) (-(i:ℤ))).toLinearEquiv.length_eq]

variable [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
lemma cyclicDuttaSequence_tendsto_oai (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F)
    (P : Ideal R) [P.IsPrime] :
    Tendsto (cyclicDuttaSequence p F P) atTop (𝓝 (cyclicDuttaContribution p F P)) := by
  classical
  let := prime_quotient_complete P
  let := isAlgClosed_quotient_residue P
  simp only [cyclicDuttaContribution,dite_eq_left (show P.IsPrime from inferInstance)]
  split_ifs with hd
  · have hG := shortComplex_quotient P hd F hF
    change Tendsto (fun n => cyclicDuttaSequence p F P n) atTop _
    simp_rw [cyclicDuttaSequence_full p F P hd]
    by_cases hzero : dimension (R ⧸ P)=0
    · exact (dutta_dimension_zero p hzero _ hG).1
    · exact CharP.exists_dutta_limit (R ⧸ P) p (Nat.pos_of_ne_zero hzero) _ hG.finiteHomology
  · exact cyclicDuttaSequence_small p F hF.finiteHomology P
      (lt_of_le_of_ne (PrimeFiltration.quotient_dimension_le P inferInstance) hd)

end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.cyclicDuttaSequence_tendsto_oai.{u} := @OAI.Lech.cyclicDuttaSequence_tendsto_oai.{u}
