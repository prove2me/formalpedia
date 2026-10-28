-- Prove2me | solution 1 for OAI.Lech.dutta_domain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:32:46.842336+00:00
-- url     : https://prove2.me/submissions/0e535716-9b67-4cbd-9985-3d9dd477bfe3

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L018
import Definitions.Def_OAIQ032L027
import Theorems.Thm_OAI_Lech_dutta_algClosed
import Theorems.Thm_OAI_Lech_finiteHomology_extendScalars
import Theorems.Thm_OAI_Lech_frobenius_shortComplex_homology_finiteLength

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra
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
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaFrobeniusShift
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra
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
-- module Solutions.OAIQ032_LECH.Multiplicity_FlatLocalSupport
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]

lemma ringKrullDim_eq_of_map_maximalIdeal
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    ringKrullDim S = ringKrullDim R := by
  have hh := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal S)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at hh
  simpa only [maximalIdeal_height_eq_ringKrullDim] using congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hh

omit [IsNoetherianRing R] [IsNoetherianRing S] in
lemma colength_eq_of_map_maximalIdeal
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) (n : ℕ) :
    colength S n = colength R n := by
  have : IsSimpleModule S (S ⧸ maximalIdeal S) :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨maximalIdeal S, inferInstance, ⟨LinearEquiv.refl S _⟩⟩
  have he := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
    ((maximalIdeal R)^n)).toLinearEquiv.length_eq
  rw [Ideal.map_pow, h] at he
  rw [IsLocalRing.length_baseChange R S (R ⧸ (maximalIdeal R)^n), h,
    Module.length_eq_one (R := S) (M := S ⧸ maximalIdeal S), mul_one] at he
  exact congrArg ENat.toNat he

lemma multiplicity_eq_of_map_maximalIdeal
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    multiplicity S = multiplicity R := by
  have hd : dimension S = dimension R := by
    unfold dimension
    rw [ringKrullDim_eq_of_map_maximalIdeal h]
  have hn : normalizedColength S = normalizedColength R := by
    funext n
    unfold normalizedColength
    rw [hd, colength_eq_of_map_maximalIdeal h]
  unfold multiplicity
  rw [hn]
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaBaseChange
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra
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
variable {R S : Type u} [CommRing R] [CommRing S]

variable [IsLocalRing R] [IsLocalRing S] [Algebra R S]
  [Module.Flat R S] [IsLocalHom (algebraMap R S)]

lemma flat_homology_length (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module.length S ((((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (.up ℤ)).obj F).homology i)=Module.length R (F.homology i) := by
  let E := ModuleCat.extendScalars (algebraMap R S)
  let : PreservesFiniteLimits E := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  rw [(flatExtensionHomologyIso (algebraMap R S)
    (RingHom.flat_algebraMap_iff.mpr inferInstance) F i).toLinearEquiv.length_eq]
  let φ := algebraMap R S
  have hflat : φ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let := φ.toAlgebra
  let : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  change Module.length S (S ⊗[R] (F.homology i))=_
  rw [IsLocalRing.length_baseChange R S (F.homology i)]
  change Module.length R (F.homology i) * Module.length S (S ⧸ (maximalIdeal R).map φ)=_
  have hm : (maximalIdeal R).map φ=maximalIdeal S := hmax
  rw [hm]
  let : IsSimpleModule S (S ⧸ maximalIdeal S) := isSimpleModule_iff_quot_maximal.mpr
    ⟨maximalIdeal S,inferInstance,⟨LinearEquiv.refl S _⟩⟩
  rw [Module.length_eq_one (R:=S) (M:=S ⧸ maximalIdeal S),mul_one]

variable [IsNoetherianRing R] [IsNoetherianRing S]
lemma dimension_eq_of_map_maximalIdeal
    (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S) : dimension S=dimension R := by
  unfold dimension
  rw [ringKrullDim_eq_of_map_maximalIdeal hmax]

lemma duttaSequence_baseChange (p : ℕ) [Fact p.Prime] [CharP R p] [CharP S p]
    (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    duttaSequence S p (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (.up ℤ)).obj F) n=duttaSequence R p F n := by
  unfold duttaSequence shortEuler
  rw [dimension_eq_of_map_maximalIdeal hmax]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have he := (homologyMapIso (frobeniusBaseChangeIso p (algebraMap R S) F n) (-(i:ℤ))).toLinearEquiv.length_eq
  rw [← he,flat_homology_length hmax]

lemma shortComplex_baseChange
    (hmax : (maximalIdeal R).map (algebraMap R S)=maximalIdeal S)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    IsShortComplex S (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (.up ℤ)).obj F) := by
  let G := (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj F)
  have hG := finiteHomology_extendScalars (algebraMap R S)
    (dimension_eq_of_map_maximalIdeal hmax)
    (by rw [hmax]; exact Ideal.IsPrime.radical inferInstance) F hF.finiteHomology
  refine ⟨hG.term_free,hG.term_finite,hG.bounded,hG.homology_finite_length,?_⟩
  intro hz
  have : Subsingleton (G.homology 0) := ModuleCat.isZero_iff_subsingleton.mp hz
  have he : Module.length R (F.homology 0)=0 :=
    (flat_homology_length hmax F 0).symm.trans (Module.length_eq_zero (R:=S) (M:=G.homology 0))
  exact hF.homology_zero_nonzero
    (ModuleCat.isZero_iff_subsingleton.mpr (Module.length_eq_zero_iff.mp he))

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaDomain
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

lemma isLocalHom_of_map_maximal {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S)
    (hmax : (maximalIdeal R).map φ=maximalIdeal S) : IsLocalHom φ := by
  constructor
  intro x hx
  by_contra hn
  have hm : x ∈ maximalIdeal R := (mem_maximalIdeal x).mpr hn
  have hm' : φ x ∈ maximalIdeal S := hmax ▸ Ideal.mem_map_of_mem φ hm
  exact hm' hx

lemma dutta_complete_charp (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    (∀ n i,IsFiniteLength R ((frobeniusComplex R p n F).homology i)) ∧
      Tendsto (duttaSequence R p F) atTop (𝓝 (duttaMultiplicity R p F)) ∧
      multiplicity R ≤ duttaMultiplicity R p F := by
  let E := residueExtension R p
  let S := E.S
  have : IsLocalHom (algebraMap R S) := isLocalHom_of_map_maximal _ E.maximal_map
  have : CharP S p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have h := congrArg (algebraMap R S) (CharP.cast_eq_zero R p)
    simpa only [map_natCast,map_zero] using h)
  let G := (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj F)
  have hG : IsShortComplex S G := shortComplex_baseChange E.maximal_map F hF
  have he : duttaSequence S p G=duttaSequence R p F :=
    funext (duttaSequence_baseChange p E.maximal_map F)
  have hm : duttaMultiplicity S p G=duttaMultiplicity R p F := congrArg (limUnder atTop) he
  obtain ⟨ht,hl⟩ := dutta_algClosed p G hG
  rw [he,hm] at ht
  rw [hm,multiplicity_eq_of_map_maximalIdeal E.maximal_map] at hl
  exact ⟨fun n i => (frobenius_finiteHomology p F hF.finiteHomology n).homology_finite_length i,ht,hl⟩

 
theorem dutta_domain_oai : DuttaDomainClaim.{u} := by
  intro D _ _ _ _ _ p _ _ F hF
  exact dutta_complete_charp D p F hF

end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.dutta_domain_oai.{u} := @OAI.Lech.dutta_domain_oai.{u}
