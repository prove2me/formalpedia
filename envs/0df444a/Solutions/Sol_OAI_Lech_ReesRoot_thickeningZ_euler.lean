-- Prove2me | solution 1 for OAI.Lech.ReesRoot.thickeningZ_euler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:36:08.262195+00:00
-- url     : https://prove2.me/submissions/1471169a-ac0c-4c23-9e5a-798e97dec8d5

import Mathlib
import Definitions.Def_OAIQ032L039
import Theorems.Thm_OAI_Lech_ReesRoot_exceptionalZ_finite
import Theorems.Thm_OAI_Lech_ReesRoot_thickeningZ_finite

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteComplexTopInclusion
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
end Lech

end

end OAI
end

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
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
variable (K L : CochainComplex (ModuleCat.{u} R) ℤ)
lemma finiteHomologyEuler_homologyIso (e : ∀ q,K.homology q ≅ L.homology q)
    (hK : ∀ q,powerTorsion I (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=finiteHomologyEuler ℓ L m N := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg ENNReal.toReal (ℓ.eq_of_iso (e (m+i)) (hK _) ((powerTorsion I).prop_of_iso (e (m+i)) (hK _)))
lemma finiteHomologyEuler_iso (e : K ≅ L)
    (hK : ∀ q,powerTorsion I (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=finiteHomologyEuler ℓ L m N :=
  finiteHomologyEuler_homologyIso ℓ K L (fun q => (homologyFunctor _ _ q).mapIso e) hK m N
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CartierQuotientDevissage
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.CartierQuotient
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L)
  (hr : ∀ q,(f.f q).hom.range=I • (⊤ : Submodule R (L.X q)))

lemma shortComplex_exact (hi : ∀ q,Function.Injective (f.f q).hom) (N : ℕ) :
    (shortComplex I f hr N).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro q
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
        change Submodule.Quotient.mk y=0 at hy
        have hm := (Submodule.Quotient.mk_eq_zero _).mp hy
        rw [←hr q] at hm
        obtain ⟨x,rfl⟩ := hm
        exact ⟨Submodule.Quotient.mk x,rfl⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((f.f q).hom x)=0 at hx
        have hm := (Submodule.Quotient.mk_eq_zero _).mp hx
        rw [←map_power I f hr N q] at hm
        obtain ⟨y,hy,he⟩ := hm
        have heq := hi q he
        subst x
        exact (Submodule.Quotient.mk_eq_zero _).mpr hy
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact ⟨Submodule.Quotient.mk x,rfl⟩
end Lech.CartierQuotient

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
-- module Solutions.OAIQ032_LECH.Multiplicity_CechCartierZRange
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (J : Ideal R)
  {M N M' N' : ModuleCat.{u} R} (f : M ⟶ N) (g : M' ⟶ N')
  (e : M' ≅ M) (e' : N' ≅ N)

lemma injective_of_square (hsq : g ≫ e'.hom=e.hom ≫ f)
    (hf : Function.Injective f.hom) : Function.Injective g.hom := by
  intro x y hxy
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  apply hf
  have hx := congrArg (fun a : M' ⟶ N => a.hom x) hsq
  have hy := congrArg (fun a : M' ⟶ N => a.hom y) hsq
  change e'.hom.hom (g.hom x)=f.hom (e.hom.hom x) at hx
  change e'.hom.hom (g.hom y)=f.hom (e.hom.hom y) at hy
  rw [←hx,←hy,hxy]
end Lech.TensorIdeal

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)

lemma cechInclusionZ_injective (a : ℕ) (q : ℤ) :
    Function.Injective ((cechInclusionZ I z hz m a).f q).hom := by
  cases q with
  | ofNat q =>
      exact TensorIdeal.injective_of_square _ _ _ _ (cechInclusionZ_square I z hz m a q)
        (cechInclusionIter_injective I z hz m a q)
  | negSucc q =>
      have hzq := cechZ_negative I z hz (raise m a) (Int.negSucc q) (by omega)
      have : Subsingleton ((cechZ I z hz (raise m a)).X (Int.negSucc q)) :=
        ModuleCat.isZero_iff_subsingleton.mp hzq
      exact Function.injective_of_subsingleton _
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


end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootThickeningEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)

lemma cechZ_bounded (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) : IsZero ((cechZ I z hz m).X q) := by
  apply FiniteModuleCech.positiveZ_bounded (cechDiagram I z hz m) q
  simp only [Fintype.card_fin]
  omega

lemma thickeningZ_bounded (N : ℕ) (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero ((thickeningZ I z hz m N).X q) :=
  (TensorIdeal.quotientFunctor (I^N)).map_isZero (cechZ_bounded I z hz m q hq)

lemma thickeningZ_homology_bounded (N : ℕ) (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero ((thickeningZ I z hz m N).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (thickeningZ_bounded I z hz m N q hq)

lemma firstZ_homology_bounded (q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero ((firstZ I z hz m).homology q) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((TensorIdeal.quotientFunctor I).map_isZero (cechZ_bounded I z hz m q hq))

lemma thickeningZ_zero : IsZero (thickeningZ I z hz m 0) := by
  apply FiniteComplex.isZero_of_X
  intro q
  change IsZero (ModuleCat.of R (((cechZ I z hz m).X q) ⧸
    (I^0 • (⊤ : Submodule R ((cechZ I z hz m).X q)))))
  rw [show I^0 • (⊤ : Submodule R ((cechZ I z hz m).X q)) = ⊤ from by
    rw [pow_zero,Ideal.one_eq_top,Submodule.top_smul]]
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

variable (hgen : Ideal.span (Set.range z)=I)

lemma thickeningShortComplex_exact (N : ℕ) : (thickeningShortComplex I z hz m hgen N).ShortExact :=
  CartierQuotient.shortComplex_exact I _ _ (cechInclusionZ_injective I z hz m 1) N

variable [LinearOrder (Chart n)] (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

include hgen hds hmu ha in
lemma firstZ_finite (q : ℤ) : ell.finiteClass ((firstZ I z hz m).homology q) :=
  ell.finiteClass.prop_of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso (firstZIso I z hz m)).symm
    (exceptionalZ_finite I z hz m hgen ell hds hmu ha q)

include hgen hds hmu ha in
lemma firstZ_euler : finiteHomologyEuler ell (firstZ I z hz m) 0 n=
    finiteHomologyEuler ell (exceptionalZ I z hz m) 0 n :=
  finiteHomologyEuler_iso ell _ _ (firstZIso I z hz m)
    (fun q => (firstZ_finite I z hz m hgen ell hds hmu ha q).1) 0 n

include hgen hds hmu ha in
 
theorem thickeningZ_euler_oai (N : ℕ) :
    finiteHomologyEuler ell (thickeningZ I z hz m N) 0 n=
      ∑ j∈Finset.range N,finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n := by
  induction N generalizing m with
  | zero =>
      simp only [Finset.range_zero,Finset.sum_empty]
      unfold finiteHomologyEuler
      apply Finset.sum_eq_zero
      intro j hj
      have hz0 : IsZero ((thickeningZ I z hz m 0).homology (0+j)) :=
        (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (0+(j:ℤ))).map_isZero (thickeningZ_zero I z hz m)
      rw [ell.realValue_zero hz0,mul_zero]
  | succ N ih =>
      have hs := thickeningShortComplex_exact I z hz m hgen N
      have he := finiteHomologyEuler_additive ell _ hs 0 n
        (thickeningZ_finite I z hz (raise m 1) hgen ell hds hmu ha N)
        (thickeningZ_finite I z hz m hgen ell hds hmu ha (N+1))
        (firstZ_finite I z hz m hgen ell hds hmu ha)
        (firstZ_homology_bounded I z hz m _ (Or.inl (by omega)))
        (thickeningZ_homology_bounded I z hz (raise m 1) N _ (Or.inr (by omega)))
      change finiteHomologyEuler ell (thickeningZ I z hz m (N+1)) 0 n=
        finiteHomologyEuler ell (thickeningZ I z hz (raise m 1) N) 0 n+
          finiteHomologyEuler ell (firstZ I z hz m) 0 n at he
      rw [he,ih,firstZ_euler I z hz m hgen ell hds hmu ha,Finset.sum_range_succ']
      congr 1

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.thickeningZ_euler_oai.{u} := @OAI.Lech.ReesRoot.thickeningZ_euler_oai.{u}
