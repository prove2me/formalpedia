-- Prove2me | solution 1 for OAI.Lech.ReesRoot.thickeningZ_finite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:36:30.510815+00:00
-- url     : https://prove2.me/submissions/f7b94fce-2daf-46b9-b27b-948bdc9c5c97

import Mathlib
import Definitions.Def_OAIQ032L039
import Theorems.Thm_OAI_Lech_ReesRoot_exceptionalZ_finite

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
lemma thickeningZ_finite_oai (N : ℕ) (q : ℤ) : ell.finiteClass ((thickeningZ I z hz m N).homology q) := by
  induction N generalizing m with
  | zero => exact ell.finiteClass.prop_of_isZero ((homologyFunctor _ _ q).map_isZero (thickeningZ_zero I z hz m))
  | succ N ih =>
      have hs := thickeningShortComplex_exact I z hz m hgen N
      exact ell.finiteClass.prop_X₂_of_exact (hs.homology_exact₂ q) (ih (raise m 1))
        (firstZ_finite I z hz m hgen ell hds hmu ha q)

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.thickeningZ_finite_oai.{u} := @OAI.Lech.ReesRoot.thickeningZ_finite_oai.{u}
