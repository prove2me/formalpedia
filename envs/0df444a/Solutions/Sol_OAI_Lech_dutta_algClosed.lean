-- Prove2me | solution 1 for OAI.Lech.dutta_algClosed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:18:16.44306+00:00
-- url     : https://prove2.me/submissions/cba0500b-ee87-466c-86da-92c9d0c9ba0a

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L002
import Definitions.Def_OAIQ032L006
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_CharP_dutta_lower_bound_infinite_perfect
import Theorems.Thm_OAI_Lech_PrimeFiltration_Factors_euler_self
import Theorems.Thm_OAI_Lech_PrimeFiltration_Factors_multiplicity_self
import Theorems.Thm_OAI_Lech_cyclicDuttaSequence_tendsto
import Theorems.Thm_OAI_Lech_dutta_dimension_zero
import Theorems.Thm_OAI_Lech_finiteHomology_extendScalars
import Theorems.Thm_OAI_Lech_frobenius_shortComplex_homology_finiteLength

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.Primary
open Filter
open scoped Topology
variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
lemma maximal_multiplicity_eq :
    multiplicity (IsLocalRing.maximalIdeal R) = Lech.multiplicity R := rfl
end Lech.Primary


open CategoryTheory
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
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimeFiltrationSupport
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.PrimeFiltration
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma next [IsNoetherianRing R] (I : Submodule R M) (hI : I ≠ ⊤) :
    ∃ J : Submodule R M, I < J ∧ ∃ p : Ideal R, p.IsPrime ∧
      Nonempty ((J.map I.mkQ) ≃ₗ[R] R ⧸ p) := by
  let : Nontrivial (M ⧸ I) := Submodule.Quotient.nontrivial_iff.mpr hI
  obtain ⟨x,hx⟩ := exists_ne (0 : M ⧸ I)
  obtain ⟨p,hp,_⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  obtain ⟨hp,y,hy⟩ := isAssociatedPrime_iff.mp hp
  let f : R →ₗ[R] M ⧸ I := LinearMap.toSpanSingleton R (M ⧸ I) y
  have hker : f.ker = p := by
    rw [hy]
    ext r
    simp only [LinearMap.mem_ker,f,LinearMap.toSpanSingleton_apply,Submodule.mem_colon_singleton,
      Submodule.mem_bot]
  have hy0 : y ≠ 0 := by
    intro hz
    apply hp.ne_top
    rw [hy,hz]
    ext r
    simp
  let J := f.range.comap I.mkQ
  have hmap : J.map I.mkQ = f.range := by
    exact Submodule.map_comap_eq_of_surjective (I.mkQ_surjective) f.range
  have hle : I ≤ J := by
    intro m hm
    change I.mkQ m ∈ f.range
    rw [Submodule.mkQ_apply,(Submodule.Quotient.mk_eq_zero I).mpr hm]
    exact Submodule.zero_mem _
  have hlt : I < J := by
    refine lt_of_le_of_ne hle ?_
    intro he
    have hz : f.range = ⊥ := by rw [←hmap,←he,Submodule.mkQ_map_self]
    have hm : y ∈ f.range := ⟨1,by simp [f]⟩
    exact hy0 (by simpa [hz] using hm)
  refine ⟨J,hlt,p,hp,?_⟩
  rw [hmap]
  have he := f.quotKerEquivRange.symm
  rw [hker] at he
  exact ⟨he⟩

theorem exists_above [IsNoetherianRing R] [Module.Finite R M] (I : Submodule R M) :
    Above I := by
  apply IsNoetherian.induction (R := R) (M := M) (P := Above) _ I
  intro I ih
  by_cases ht : I = ⊤
  · rw [ht]
    exact .top
  · obtain ⟨J,hJ,p,hp,e⟩ := next I ht
    exact .cons I J hJ.le p hp e (ih J hJ)
end Lech.PrimeFiltration

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

end Lech.PrimeFiltration

namespace Lech.PrimeFiltration
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma factors_of_above {N : Submodule R M} (h : Above N) : ∃ ps, Factors N ps := by
  induction h with
  | top => exact ⟨[],.top⟩
  | cons N J hNJ p hp e tail ih =>
    obtain ⟨ps,hps⟩ := ih
    exact ⟨p::ps,.cons N J hNJ p hp e hps⟩

lemma Factors.isPrime {N : Submodule R M} {ps : List (Ideal R)} (h : Factors N ps) :
    ∀ p ∈ ps, p.IsPrime := by
  induction h with
  | top => simp
  | cons N J hNJ q hq e tail ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hq
    · exact ih p hp

open scoped TensorProduct

open Filter IsLocalRing
open scoped Topology
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

variable [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]

attribute [local instance] OAI.Lech.duttaQuotientCharP
lemma cyclicDuttaContribution_lower (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F)
    (P : Ideal R) [P.IsPrime] :
    ((dimension R).factorial:ℝ) * PrimeFiltration.contribution (maximalIdeal R) P ≤
      cyclicDuttaContribution p F P := by
  classical
  let := prime_quotient_complete P
  let := isAlgClosed_quotient_residue P
  simp only [cyclicDuttaContribution,PrimeFiltration.contribution,
    dite_eq_left (show P.IsPrime from inferInstance)]
  split_ifs with hd
  · rw [map_maximalIdeal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
      Primary.maximal_multiplicity_eq]
    have hfac : ((dimension R).factorial:ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hfac]
    have hG := shortComplex_quotient P hd F hF
    by_cases hzero : dimension (R ⧸ P)=0
    · exact (dutta_dimension_zero p hzero _ hG).2
    · exact CharP.dutta_lower_bound_infinite_perfect (R ⧸ P) p (Nat.pos_of_ne_zero hzero) _ hG
  · simp
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaAlgClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]

lemma dutta_algClosed_oai (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    Tendsto (duttaSequence R p F) atTop (𝓝 (duttaMultiplicity R p F)) ∧
      multiplicity R ≤ duttaMultiplicity R p F := by
  classical
  obtain ⟨ps,hps⟩ := PrimeFiltration.factors_of_above
    (PrimeFiltration.exists_above (⊥ : Submodule R R))
  have he (n : ℕ) : duttaSequence R p F n=
      (ps.map (fun P => cyclicDuttaSequence p F P n)).sum := by
    unfold duttaSequence cyclicDuttaSequence
    rw [List.sum_map_mul_left,hps.euler_self _ (frobenius_finiteHomology p F hF.finiteHomology n)]
  have ht := tendsto_list_sum ps (fun P hP => by
    have := hps.isPrime P hP
    exact cyclicDuttaSequence_tendsto p F hF P)
  have ht' : Tendsto (duttaSequence R p F) atTop
      (𝓝 (ps.map (cyclicDuttaContribution p F)).sum) := ht.congr (fun n => (he n).symm)
  have hl : duttaMultiplicity R p F=(ps.map (cyclicDuttaContribution p F)).sum := ht'.limUnder_eq
  rw [hl]
  refine ⟨ht',?_⟩
  rw [hps.multiplicity_self]
  apply List.sum_le_sum
  intro P hP
  have := hps.isPrime P hP
  exact cyclicDuttaContribution_lower p F hF P
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.dutta_algClosed_oai.{u} := @OAI.Lech.dutta_algClosed_oai.{u}
