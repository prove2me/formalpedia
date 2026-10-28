-- Prove2me | solution 1 for OAI.Lech.ReesRoot.unfilteredEuler_affine_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:10:56.43903+00:00
-- url     : https://prove2.me/submissions/bdd895b7-def1-4ec9-897f-96d30a7adea6

import Mathlib
import Definitions.Def_OAIQ032L038
import Theorems.Thm_OAI_Lech_ReesRoot_unfilteredTotal_finite

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
include hS in
 

theorem finiteHomologyEuler_additive (m : ℤ) (N : ℕ)
    (h₁ : ∀ i,ℓ.finiteClass (S.X₁.homology i))
    (h₂ : ∀ i,ℓ.finiteClass (S.X₂.homology i))
    (h₃ : ∀ i,ℓ.finiteClass (S.X₃.homology i))
    (hl : IsZero (S.X₃.homology (m-1))) (hr : IsZero (S.X₁.homology (m+N+1))) :
    finiteHomologyEuler ℓ S.X₂ m N=finiteHomologyEuler ℓ S.X₁ m N+finiteHomologyEuler ℓ S.X₃ m N := by
  let a (i : ℕ) := ℓ.realValue (image (hS.δ (m+i-1) (m+i) (by change m+i-1+1=m+i;omega)))
  have hi (i : ℕ) : ℓ.realValue (S.X₁.homology (m+i))-ℓ.realValue (S.X₂.homology (m+i))+
      ℓ.realValue (S.X₃.homology (m+i))=a i+a (i+1) := by
    rw [homology_length_defect ℓ S hS (m+i) (h₁ _) (h₂ _) (h₃ _)]
    have hδ (j j' k k' : ℤ) (hjk : j+1=k) (hjk' : j'+1=k')
        (hj : j=j') (hk : k=k') :
        ℓ.realValue (image (hS.δ j k hjk))=ℓ.realValue (image (hS.δ j' k' hjk')) := by
      subst j';subst k';rfl
    exact congrArg (a i + ·) (hδ _ _ _ _ rfl _ (by push_cast;omega) (by push_cast;omega))
  have ha₀ : a 0=0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_epi (factorThruImage (hS.δ (m+0-1) (m+0) (by change m+0-1+1=m+0;omega)))
    simpa using hl
  have ha₁ : a (N+1)=0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_mono (Limits.image.ι (hS.δ (m+(N+1)-1) (m+(N+1)) (by change m+(N+1)-1+1=m+(N+1);omega)))
    simpa [Nat.cast_add,Nat.cast_one,add_assoc] using hr
  have he : finiteHomologyEuler ℓ S.X₁ m N-finiteHomologyEuler ℓ S.X₂ m N+
      finiteHomologyEuler ℓ S.X₃ m N=0 := by
    calc
      _=∑ i ∈ Finset.range (N+1),(-1:ℝ)^i*(ℓ.realValue (S.X₁.homology (m+i))-
          ℓ.realValue (S.X₂.homology (m+i))+ℓ.realValue (S.X₃.homology (m+i))) := by
        simp only [finiteHomologyEuler,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]
      _=a 0+(-1:ℝ)^N*a (N+1) := by
        simp_rw [hi]
        exact alternating_sum_pairs a N
      _=0 := by rw [ha₀,ha₁,mul_zero,add_zero]
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
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Set
open AlternatingCech
universe u
variable (R : Type u) [CommRing R] (ι : Type) [Fintype ι] [LinearOrder ι]



variable {R ι}
variable (D : Diagram R ι)

lemma bounded (n : ℕ) (hn : Fintype.card ι < n) : IsZero ((complex D).X n) := by
  have : Subsingleton (cochains D n) := ⟨fun f g => funext fun s => by
    have hs : s.val.card = n := s.property
    have hl := Finset.card_le_univ s.val
    omega⟩
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (cochains D n))

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]



lemma positiveComplex_bounded (D : Diagram R ι) (n : ℕ) (hn : Fintype.card ι ≤ n) :
    IsZero ((positiveComplex D).X n) := bounded D (n+1) (by omega)

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechExact
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] {ι : Type}
variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)

lemma cochains_shortExact (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact) (q : ℕ) :
    (cochainsShortComplex φ ψ hzero q).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    funext s
    exact (hs s.val).moduleCat_injective_f (congrFun hxy s))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    intro y
    choose x hx using fun s : Set.powersetCard ι q => (hs s.val).moduleCat_surjective_g (y s)
    exact ⟨x,funext hx⟩)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    have hys (s : Set.powersetCard ι q) : (ψ.app s.val).hom (y s)=0 := congrFun hy s
    choose x hx using fun s : Set.powersetCard ι q =>
      (ShortComplex.moduleCat_exact_iff _).mp (hs s.val).exact (y s) (hys s)
    exact ⟨x,funext hx⟩)

variable [Fintype ι] [LinearOrder ι]

lemma positive_shortExact (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact) :
    (positiveShortComplex φ ψ hzero).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun q => cochains_shortExact φ ψ hzero hs (q+1))

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CechProducts
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type}
variable (D E : Diagram R ι)

variable {D E} {G : Diagram R ι}

variable (D E)
lemma prod_shortExact (s : Finset ι) :
    (diagramShortComplex (prodInl D E) (prodSnd D E) (prod_comp_zero D E) s).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y h
    exact congrArg Prod.fst h)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (fun y => ⟨(0,y),rfl⟩)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    exact ⟨y.1,Prod.ext rfl hy.symm⟩)
end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechMapCochain
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex


namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

lemma extend_shortExact (S : ShortComplex (HomologicalComplex C c)) (hS : S.ShortExact)
    (e : c.Embedding c') : (S.map (e.extendFunctor C)).ShortExact := by
  classical
  apply shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : ∃ i, e.f i=j
  · obtain ⟨i,hi⟩ := hj
    apply ShortComplex.shortExact_of_iso (ShortComplex.isoMk
      (S.X₁.extendXIso e hi) (S.X₂.extendXIso e hi) (S.X₃.extendXIso e hi)
      ?_ ?_).symm (hS.map_of_exact (eval C c i))
    · change _ = (extendMap S.f e).f j ≫ _
      rw [extendMap_f _ _ hi]
      simp
      all_goals rfl
    · change _ = (extendMap S.g e).f j ≫ _
      rw [extendMap_f _ _ hi]
      simp
      all_goals rfl
  · have hnone : ∀ i, e.f i≠j := by simpa using hj
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ (S.X₂.isZero_extend_X e j hnone)
            mono_f := (S.X₁.isZero_extend_X e j hnone).mono _
            epi_g := (S.X₃.isZero_extend_X e j hnone).epi _ }
end Lech


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category J]

lemma functorCategory_shortExact (S : ShortComplex (J ⥤ C))
    (hS : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact := by
  have hm : ∀ j, Mono (S.f.app j) := fun j => (hS j).mono_f
  have he : ∀ j, Epi (S.g.app j) := fun j => (hS j).epi_g
  refine {exact := ?_, mono_f := ?_, epi_g := ?_}
  · apply S.exact_of_f_is_kernel
    apply evaluationJointlyReflectsLimits
    intro j
    have := (hS j).mono_f
    exact (KernelFork.isLimitMapConeEquiv _ _).symm ((hS j).exact.fIsKernel)
  · exact NatTrans.mono_of_mono_app S.f
  · exact NatTrans.epi_of_epi_app S.g

variable {ι : Type w}

lemma discreteShortComplex_shortExact (S : ι → ShortComplex C)
    (hS : ∀ i, (S i).ShortExact) : (discreteShortComplex S).ShortExact := by
  apply functorCategory_shortExact
  intro i
  exact hS i.as

variable [HasCoproductsOfShape ι C] [HasExactColimitsOfShape (Discrete ι) C]
lemma coproduct_shortExact (S : ι → ShortComplex C) (hS : ∀ i, (S i).ShortExact) :
    ((discreteShortComplex S).map (colim (J:=Discrete ι) (C:=C))).ShortExact :=
  (discreteShortComplex_shortExact S hS).map_of_exact _
end Lech


namespace Lech.TensorTotal.Right
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)



lemma shortExact (hK : ∀ p, Module.Flat R (K.X p))
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact) :
    (S.map (functor K)).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  apply ShortComplex.shortExact_of_iso (degreeSequenceIso K S i)
  apply Lech.coproduct_shortExact
  intro pq
  have := hK pq.1.1
  exact (hS.map_of_exact (eval (ModuleCat.{u} R) (.up ℤ) pq.1.2)).map_of_exact
    (tensorLeft (K.X pq.1.1))
end Lech.TensorTotal.Right
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex FiniteModuleCech
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (m : Fin n → ℤ) (i : Fin n)

lemma eulerCech_shortExact (s : Finset (Fin (n+1))) :
    (diagramShortComplex (eulerCechLeft I z hz m i) (eulerCechRight I z hz m i)
      (eulerCech_zero I z hz m i) s).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    funext hs
    apply (euler_shortExact I z hz s hs.down m i).1
    exact Prod.ext (congrFun (congrArg Prod.fst hxy) hs) (congrFun (congrArg Prod.snd hxy) hs))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (by
    intro y
    choose x hx using fun hs : PLift s.Nonempty => (euler_shortExact I z hz s hs.down m i).2.2 (y hs)
    exact ⟨(fun hs => (x hs).1,fun hs => (x hs).2),funext hx⟩)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    have hys (hs : PLift s.Nonempty) : eulerRight I z hz s hs.down m i (y.1 hs,y.2 hs)=0 := congrFun hy hs
    choose x hx using fun hs : PLift s.Nonempty =>
      (euler_shortExact I z hz s hs.down m i).2.1 (y.1 hs,y.2 hs) |>.mp (hys hs)
    exact ⟨x,Prod.ext (funext (fun hs => congrArg Prod.fst (hx hs)))
      (funext (fun hs => congrArg Prod.snd (hx hs)))⟩)



end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCechEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [LinearOrder ι]


lemma positiveZ_bounded (D : Diagram R ι) (q : ℤ)
    (hq : q < 0 ∨ (Fintype.card ι:ℤ) ≤ q) : IsZero ((positiveZ D).X q) := by
  by_cases hq0 : 0 ≤ q
  · have he : ComplexShape.embeddingUpNat.f q.toNat=q := Int.toNat_of_nonneg hq0
    exact (positiveComplex_bounded D q.toNat (by omega)).of_iso
      ((positiveComplex D).extendXIso ComplexShape.embeddingUpNat he)
  · apply (positiveComplex D).isZero_extend_X
    intro j hj
    change (j:ℤ)=q at hj
    omega


lemma tensorCech_bounded (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p)) (D : Diagram R ι)
    (q : ℤ) (hq : q < -(h:ℤ) ∨ (Fintype.card ι:ℤ) ≤ q) :
    IsZero ((tensorCech F D).X q) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply mapBifunctor.hom_ext
  intro p r hpr
  have hz : IsZero ((F.X p) ⊗ (positiveZ D).X r) := by
    by_cases hp : p < -(h:ℤ) ∨ 0<p
    · exact (tensorRight ((positiveZ D).X r)).map_isZero (hb p hp)
    · exact (tensorLeft (F.X p)).map_isZero
        (positiveZ_bounded D r (by change p+r=q at hpr; omega))
  exact hz.eq_of_src _ _

lemma tensorCech_homology_bounded (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p)) (D : Diagram R ι)
    (q : ℤ) (hq : q < -(h:ℤ) ∨ (Fintype.card ι:ℤ) ≤ q) :
    IsZero ((tensorCech F D).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (tensorCech_bounded F h hb D q hq)

variable {D E G : Diagram R ι} (φ : Map D E) (ψ : Map E G)
  (hzero : ∀ s,φ.app s ≫ ψ.app s=0)


lemma tensorShortComplex_shortExact (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact) :
    (tensorShortComplex φ ψ hzero F).ShortExact :=
  TensorTotal.Right.shortExact F hflat _
    (extend_shortExact _ (positive_shortExact φ ψ hzero hs) _)

variable {I : Ideal R} (ell : TorsionLength I)

lemma tensorEuler_additive (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (hs : ∀ s,(diagramShortComplex φ ψ hzero s).ShortExact)
    (hD : ∀ q,ell.finiteClass ((tensorCech F D).homology q))
    (hG : ∀ q,ell.finiteClass ((tensorCech F G).homology q)) :
    tensorEuler ell F h E=tensorEuler ell F h D+tensorEuler ell F h G := by
  have hS := tensorShortComplex_shortExact φ ψ hzero F hflat hs
  have hE (q : ℤ) : ell.finiteClass ((tensorCech F E).homology q) :=
    ell.finiteClass.prop_X₂_of_exact (hS.homology_exact₂ q) (hD q) (hG q)
  have he := finiteHomologyEuler_additive ell _ hS (-(h:ℤ)) (h+Fintype.card ι)
    hD hE hG (tensorCech_homology_bounded F h hb G _ (by omega))
    (tensorCech_homology_bounded F h hb D _ (by omega))
  change finiteHomologyEuler ell (tensorCech F E) _ _ = _ at he
  unfold tensorEuler
  rw [he,mul_add]
  rfl

lemma tensorEuler_prod (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
    (hflat : ∀ p,Module.Flat R (F.X p))
    (D E : Diagram R ι)
    (hD : ∀ q,ell.finiteClass ((tensorCech F D).homology q))
    (hE : ∀ q,ell.finiteClass ((tensorCech F E).homology q)) :
    tensorEuler ell F h (prodDiagram D E)=tensorEuler ell F h D+tensorEuler ell F h E :=
  tensorEuler_additive (prodInl D E) (prodSnd D E) (prod_comp_zero D E)
    ell F h hb hflat (prod_shortExact D E) hD hE

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEulerFunction
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)


variable [LinearOrder (Chart n)]
  (hgen : Ideal.span (Set.range z)=I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in
lemma unfilteredEuler_affine_step_oai (m : Fin n → ℤ) (i : Fin n) :
    unfilteredEuler I z hz ell F h m+unfilteredEuler I z hz ell F h (Pi.single i 1+(Pi.single i 1+m))=
      2*unfilteredEuler I z hz ell F h (Pi.single i 1+m) := by
  have hf (m : Fin n → ℤ) (q : ℤ) : ell.finiteClass ((tensorCech F (cechDiagram I z hz m)).homology q) :=
    unfilteredTotal_finite I z hz F h m hgen ell hds hmu ha b B hflat hp hfin hb hac q
  have he := tensorEuler_additive (eulerCechLeft I z hz m i) (eulerCechRight I z hz m i)
    (eulerCech_zero I z hz m i) ell F h hb hflat (eulerCech_shortExact I z hz m i) (hf m) (hf _)
  have hg := tensorEuler_prod ell F h hb hflat (cechDiagram I z hz (Pi.single i 1+m))
    (cechDiagram I z hz (Pi.single i 1+m)) (hf _) (hf _)
  change tensorEuler ell F h (prodDiagram _ _)=_ at he
  rw [hg] at he
  change _+_=2*_ 
  dsimp only [unfilteredEuler]
  linarith

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.unfilteredEuler_affine_step_oai.{u} := @OAI.Lech.ReesRoot.unfilteredEuler_affine_step_oai.{u}
