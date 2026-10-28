-- Prove2me | solution 1 for OAI.Lech.PrimeFiltration.Factors.euler_self
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:13:45.484992+00:00
-- url     : https://prove2.me/submissions/6eb84fc8-533f-4c3f-837a-1a9a53a598b9

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L013
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L017
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_shortComplex_nullScalar_radical

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian

open scoped BigOperators
namespace Lech

section

section
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}
namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma additive_real {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) (hM : ℓ.finiteClass S.X₂) :
    ℓ.realValue S.X₂ = ℓ.realValue S.X₁ + ℓ.realValue S.X₃ := by
  have := hS.mono_f
  have := hS.epi_g
  have h₁ := ℓ.finiteClass.prop_of_mono S.f hM
  have h₃ := ℓ.finiteClass.prop_of_epi S.g hM
  exact (congrArg ENNReal.toReal (ℓ.additive hS hM.1)).trans
    (ENNReal.toReal_add h₁.2 h₃.2)

lemma realValue_zero {M : ModuleCat.{u} R} (hM : IsZero M) :
    ℓ.realValue M = 0 := by simp [realValue, ℓ.zero hM]

lemma exact_real_image_sum (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.Exact) (hM : ℓ.finiteClass S.X₂) :
    ℓ.realValue S.X₂ = ℓ.realValue (image S.f) + ℓ.realValue (image S.g) := by
  let T := ShortComplex.mk (Limits.image.ι S.f) S.g (image_ι_comp_eq_zero S.zero)
  have hT : T.Exact := T.exact_of_f_is_kernel hS.isLimitImage'
  let U := ShortComplex.mk T.f (factorThruImage T.g)
    (comp_factorThruImage_eq_zero T.zero)
  have hU : U.ShortExact :=
    { exact := U.exact_of_g_is_cokernel hT.isColimitImage
      mono_f := (inferInstance : Mono (Limits.image.ι S.f))
      epi_g := (inferInstance : Epi (factorThruImage T.g)) }
  exact ℓ.additive_real hU hM

end TorsionLength

lemma alternating_sum_pairs (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * (a i + a (i + 1)) =
      a 0 + (-1 : ℝ) ^ n * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring


end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)


variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
lemma homology_length_defect (j : ℤ)
    (h₁ : ℓ.finiteClass (S.X₁.homology j))
    (h₂ : ℓ.finiteClass (S.X₂.homology j))
    (h₃ : ℓ.finiteClass (S.X₃.homology j)) :
    ℓ.realValue (S.X₁.homology j)-ℓ.realValue (S.X₂.homology j)+ℓ.realValue (S.X₃.homology j)=
      ℓ.realValue (image (hS.δ (j-1) j (by change j-1+1=j;omega)))+
      ℓ.realValue (image (hS.δ j (j+1) rfl)) := by
  have h1 := ℓ.exact_real_image_sum _ (hS.homology_exact₁ (j-1) j (by change j-1+1=j;omega)) h₁
  have h2 := ℓ.exact_real_image_sum _ (hS.homology_exact₂ j) h₂
  have h3 := ℓ.exact_real_image_sum _ (hS.homology_exact₃ j (j+1) rfl) h₃
  dsimp only at h1 h2 h3
  linarith
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleTensor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
namespace Lech
variable {A : Type*} [CommRing A]

lemma length_le_quotient_generators {N : Type*} [AddCommGroup N] [Module A N]
    (I : Ideal A) (hI : I ≤ Module.annihilator A N)
    {b : ℕ} (f : (Fin b → A) →ₗ[A] N) (hf : Function.Surjective f) :
    Module.length A N ≤ b * Module.length A (A ⧸ I) := by
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
    Module.length A N ≤ Module.length A ((Fin b → A) ⧸ P) :=
      Module.length_le_of_surjective q hq
    _ = Module.length A (Fin b → A ⧸ I) :=
      (Submodule.quotientPi (fun _ : Fin b => I)).length_eq
    _ = _ := by simp

open Filter
open scoped Topology


end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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



theorem quotient_length_ne_top (A : Type*) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (N : ℕ) :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N) ≠ ⊤ := by
  by_cases hN : N = 0
  · subst N
    simp
  · let I := (IsLocalRing.maximalIdeal A) ^ N
    have hp : IsLocalRing.maximalIdeal A ∈ I.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow _ hN,
        Ideal.IsPrime.radical inferInstance, Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton _
    let : IsArtinianRing (A ⧸ I) :=
      IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I hp
    rw [Module.length_eq_of_surjective (R := A ⧸ I)
      (by simpa only [Ideal.Quotient.algebraMap_eq] using
        (Ideal.Quotient.mk_surjective (I := I)))]
    exact Module.length_ne_top


end Lech
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechLengthLe
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma length_quotient_le {I J : Ideal R} (h : I ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ I) := by
  let f := I.mapQ J LinearMap.id h
  apply Module.length_le_of_surjective f
  intro q
  obtain ⟨r, rfl⟩ := J.mkQ_surjective q
  exact ⟨I.mkQ r, rfl⟩

end Lech

open scoped BigOperators
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedLengthPiece
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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

lemma exists_maximal_pow_le (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, (IsLocalRing.maximalIdeal R) ^ a ≤ I := by
  simpa only [hI] using I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing

lemma length_ne_top (I : Ideal R) (hI : I.radical = IsLocalRing.maximalIdeal R) (N : ℕ) :
    Module.length R (R ⧸ I ^ N) ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_maximal_pow_le I hI
  have hle := Lech.length_quotient_le R (show
    (IsLocalRing.maximalIdeal R) ^ (a * N) ≤ I ^ N by
      rw [pow_mul]
      exact pow_le_pow_left' ha N)
  exact ne_top_of_le_ne_top (Lech.quotient_length_ne_top R (a * N)) hle

end Lech.Primary


open CategoryTheory
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusFiniteLength
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open scoped TensorProduct
universe u

lemma finiteLength_of_primary_annihilator {S N : Type*} [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [AddCommGroup N] [Module S N] [Module.Finite S N]
    (I : Ideal S) (hI : I.radical = IsLocalRing.maximalIdeal S)
    (hIN : I ≤ Module.annihilator S N) : IsFiniteLength S N := by
  obtain ⟨b,f,hf⟩ := Module.Finite.exists_fin' S N
  apply Module.length_ne_top_iff.mp
  have hIfin := Lech.Primary.length_ne_top I hI 1
  rw [pow_one] at hIfin
  exact ne_top_of_le_ne_top (WithTop.mul_ne_top (ENat.natCast_ne_top b) hIfin)
    (length_le_quotient_generators I hIN f hf)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyFinite
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma finite_shortComplex_homology [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₂] :
    Module.Finite R S.homology := by
  let : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R ((LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

lemma finite_cochain_homology [IsNoetherianRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) [Module.Finite R (F.X i)] :
    Module.Finite R (F.homology i) := by
  let : Module.Finite R (F.sc i).X₂ := by
    change Module.Finite R (F.X i)
    infer_instance
  exact finite_shortComplex_homology (F.sc i)

lemma finiteLength_of_maximal_le_radical_annihilator [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : IsLocalRing.maximalIdeal R ≤ (Module.annihilator R M).radical) :
    IsFiniteLength R M := by
  apply finiteLength_of_primary_annihilator
    (Module.annihilator R M ⊓ IsLocalRing.maximalIdeal R) _ inf_le_left
  rw [Ideal.radical_inf,(IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical,
    inf_eq_right.mpr hM]


end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorEuler
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma ordinaryLength_real [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{u} R) :
    (ordinaryLength (⊥:Ideal R)).realValue M=((Module.length R M).toNat:ℝ) := by
  change (Module.length R M).toENNReal.toReal=_
  rcases eq_or_ne (Module.length R M) ⊤ with h|h
  · simp [h]
  · obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp h
    rw [← hn]
    simp

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma ordinaryLength_finite [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) :
    (ordinaryLength (⊥:Ideal R)).finiteClass M := by
  refine ⟨⟨1,by simp⟩,?_⟩
  change (Module.length R M).toENNReal ≠ ⊤
  simpa using Module.length_ne_top_iff.mpr hM

lemma shortEuler_additive
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (h₁ : ∀ i,IsFiniteLength R (S.X₁.homology i))
    (h₂ : ∀ i,IsFiniteLength R (S.X₂.homology i))
    (h₃ : ∀ i,IsFiniteLength R (S.X₃.homology i))
    (hl : IsZero (S.X₃.homology (-(dimension R:ℤ)-1)))
    (hr : IsZero (S.X₁.homology 1)) :
    shortEuler R S.X₂=shortEuler R S.X₁+shortEuler R S.X₃ := by
  let ell := ordinaryLength (⊥:Ideal R)
  let a (i : ℕ) := ell.realValue (image (hS.δ (-(i:ℤ)) (-(i:ℤ)+1) rfl))
  have hi (i : ℕ) :
      ell.realValue (S.X₁.homology (-(i:ℤ)))-ell.realValue (S.X₂.homology (-(i:ℤ)))+
        ell.realValue (S.X₃.homology (-(i:ℤ)))=a i+a (i+1) := by
    rw [homology_length_defect ell S hS (-(i:ℤ))
      (ordinaryLength_finite _ (h₁ _)) (ordinaryLength_finite _ (h₂ _))
      (ordinaryLength_finite _ (h₃ _))]
    change _+a i=_
    rw [add_comm (a i)]
    congr 1
    have hδ (j j' k k' : ℤ) (hjk : j+1=k) (hjk' : j'+1=k')
        (hj : j=j') (hk : k=k') :
        ell.realValue (image (hS.δ j k hjk))=ell.realValue (image (hS.δ j' k' hjk')) := by
      subst j';subst k';rfl
    exact hδ _ _ _ _ _ _ (by push_cast;omega) (by push_cast;omega)
  have ha₀ : a 0=0 := by
    apply ell.realValue_zero
    apply IsZero.of_mono (image.ι (hS.δ 0 1 rfl))
    exact hr
  have ha₁ : a (dimension R+1)=0 := by
    apply ell.realValue_zero
    apply IsZero.of_epi (factorThruImage (hS.δ (-((dimension R+1:ℕ):ℤ))
      (-((dimension R+1:ℕ):ℤ)+1) rfl))
    convert hl using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    push_cast
    omega
  have he : shortEuler R S.X₁-shortEuler R S.X₂+shortEuler R S.X₃=0 := by
    calc
      _=∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
          (ell.realValue (S.X₁.homology (-(i:ℤ)))-ell.realValue (S.X₂.homology (-(i:ℤ)))+
            ell.realValue (S.X₃.homology (-(i:ℤ)))) := by
        simp only [ell,ordinaryLength_real,shortEuler,mul_add,mul_sub,
          Finset.sum_add_distrib,Finset.sum_sub_distrib]
      _=a 0+(-1:ℝ)^dimension R*a (dimension R+1) := by
        simp_rw [hi]
        exact alternating_sum_pairs a (dimension R)
      _=0 := by rw [ha₀,ha₁,mul_zero,add_zero]
  linarith

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma tensorModule_shortExact [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ i,Module.Flat R (F.X i))
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (tensorModuleFunctor F)).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  let := hflat i
  let := hS.mono_f
  let := hS.epi_g
  exact hS.map (tensorLeft (F.X i))

lemma tensorModule_homology_finite (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℤ) :
    IsFiniteLength R (((tensorModuleFunctor F).obj M).homology i) := by
  let G := (tensorModuleFunctor F).obj M
  have : Module.Finite R (G.X i) := by
    have := hF.term_finite i
    change Module.Finite R ((F.X i) ⊗[R] M)
    infer_instance
  have := finite_cochain_homology G i
  apply finiteLength_of_maximal_le_radical_annihilator
  intro x hx
  obtain ⟨a,ha⟩ := shortComplex_nullScalar_radical F hF hx
  refine ⟨a,?_⟩
  apply Koszul.scalar_annihilates_homology G (x^a) _ i
  have H := (((curriedTensor (ModuleCat.{u} R)).flip.obj M).mapHomotopy ha.some)
  have he : (TensorTotal.termTensor M).map (x^a • 𝟙 F)=x^a • 𝟙 G := by
    ext j : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext y z
    rfl
  rw [he, CategoryTheory.Functor.map_zero] at H
  exact H

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma tensorModule_homology_bounded [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (M : ModuleCat.{u} R) (i : ℤ)
    (hi : i < -(dimension R:ℤ) ∨ 0 < i) :
    IsZero (((tensorModuleFunctor F).obj M).homology i) :=
  (ExactAt.of_isZero (((curriedTensor (ModuleCat.{u} R)).flip.obj M).map_isZero
    (hF.bounded i hi))).isZero_homology

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma shortEuler_eq_of_iso [IsNoetherianRing R] [IsLocalRing R]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (e : F ≅ G) :
    shortEuler R F=shortEuler R G := by
  unfold shortEuler
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homologyMapIso e (-(i:ℤ))).toLinearEquiv.length_eq]

lemma tensorEuler_equiv (F : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R M))=
      shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R N)) :=
  shortEuler_eq_of_iso ((tensorModuleFunctor F).mapIso e.toModuleIso)

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimeFiltrationEuler
attribute [-instance] _root_.OAI.Lech.Homogeneous.awayAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

lemma tensorEuler_submodule
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M) :
    shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R M))=
      shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R N))+
      shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (M ⧸ N))) := by
  let S := ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext x; simp)
  have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S
    (by change Function.Exact N.subtype N.mkQ; exact LinearMap.exact_iff.mpr (by simp))
    N.injective_subtype N.mkQ_surjective
  have hT := tensorModule_shortExact F (fun i => by have := hF.term_free i; infer_instance) S hS
  apply shortEuler_additive (S.map (tensorModuleFunctor F)) hT
  · exact tensorModule_homology_finite F hF (ModuleCat.of R N)
  · exact tensorModule_homology_finite F hF (ModuleCat.of R M)
  · exact tensorModule_homology_finite F hF (ModuleCat.of R (M ⧸ N))
  · exact tensorModule_homology_bounded F hF (ModuleCat.of R (M ⧸ N)) _ (Or.inl (by omega))
  · exact tensorModule_homology_bounded F hF (ModuleCat.of R N) _ (Or.inr (by omega))

namespace PrimeFiltration
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
lemma Factors.tensorEuler {N : Submodule R M} {ps : List (Ideal R)} (h : Factors N ps)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (M ⧸ N)))=
      (ps.map (fun P => shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))))).sum := by
  induction h with
  | top =>
      have hz := (tensorModuleFunctor F).map_isZero
        ((ModuleCat.isZero_iff_subsingleton (M:=ModuleCat.of R (M ⧸ (⊤:Submodule R M)))).mpr inferInstance)
      simp only [List.map_nil,List.sum_nil,shortEuler]
      apply Finset.sum_eq_zero
      intro i hi
      have : Subsingleton (((tensorModuleFunctor F).obj (ModuleCat.of R (M ⧸ (⊤:Submodule R M)))).homology (-(i:ℤ))) :=
        ModuleCat.isZero_iff_subsingleton.mp ((homologyFunctor _ _ (-(i:ℤ))).map_isZero hz)
      simp
  | @cons N J hNJ P hP e qs tail ih =>
      obtain ⟨e⟩ := e
      rw [tensorEuler_submodule F hF (J.map N.mkQ),tensorEuler_equiv F e,
        tensorEuler_equiv F (Submodule.quotientQuotientEquivQuotient N J hNJ),ih]
      rfl

lemma Factors.euler_self_oai {ps : List (Ideal R)} (h : Factors (⊥ : Submodule R R) ps)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    shortEuler R F=
      (ps.map (fun P => shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))))).sum := by
  have he := h.tensorEuler F hF
  rw [tensorEuler_equiv F (Submodule.quotEquivOfEqBot _ rfl),
    shortEuler_eq_of_iso (tensorModuleUnitIso F)] at he
  exact he
end PrimeFiltration
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.PrimeFiltration.Factors.euler_self_oai.{u} := @OAI.Lech.PrimeFiltration.Factors.euler_self_oai.{u}
