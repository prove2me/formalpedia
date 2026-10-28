-- Prove2me | solution 1 for OAI.Lech.ReesRoot.unfilteredEuler_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:36:52.805668+00:00
-- url     : https://prove2.me/submissions/d12e3ff6-33d9-4ff4-8152-99995d72fbe0

import Mathlib
import Definitions.Def_OAIQ032L039
import Theorems.Thm_OAI_Lech_FiniteModuleCech_tensor_euler_rank_zero
import Theorems.Thm_OAI_Lech_ReesRoot_exceptionalZ_finite
import Theorems.Thm_OAI_Lech_ReesRoot_unfilteredTotal_finite

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
variable {R : Type u} [CommRing R] {I : Ideal R}

lemma powerTorsion_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    powerTorsion I (ModuleCat.of R (M × N)) := by
  obtain ⟨a, ha⟩ := hM
  obtain ⟨b, hb⟩ := hN
  refine ⟨max a b, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext
  · exact Module.mem_annihilator.mp (ha (Ideal.pow_le_pow_right (le_max_left a b) hr)) x.1
  · exact Module.mem_annihilator.mp (hb (Ideal.pow_le_pow_right (le_max_right a b) hr)) x.2

lemma powerTorsion_fin {M : Type u} [AddCommGroup M] [Module R M] (n : ℕ)
    (hM : powerTorsion I (ModuleCat.of R M)) :
    powerTorsion I (ModuleCat.of R (Fin n → M)) := by
  obtain ⟨a, ha⟩ := hM
  refine ⟨a, ?_⟩
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  ext i
  exact Module.mem_annihilator.mp (ha hr) (x i)

namespace TorsionLength
variable (ℓ : TorsionLength I)

lemma additive_linear {M N P : Type u} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f)
    (hg : Function.Surjective g) (he : Function.Exact f g)
    (ht : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R N) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R P) := by
  let S := ShortComplex.moduleCatMk f g (LinearMap.range_le_ker_iff.mp
    ((LinearMap.exact_iff.mp he).symm.le))
  have hS : S.ShortExact :=
    { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr he
      mono_f := (ModuleCat.mono_iff_injective _).mpr hf
      epi_g := (ModuleCat.epi_iff_surjective _).mpr hg }
  exact ℓ.additive hS ht

lemma value_prod {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    (hM : powerTorsion I (ModuleCat.of R M)) (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R (M × N)) =
      ℓ.value (ModuleCat.of R M) + ℓ.value (ModuleCat.of R N) := by
  apply ℓ.additive_linear (LinearMap.inl R M N) (LinearMap.snd R M N)
  · intro x y h
    exact congrArg Prod.fst h
  · intro n
    exact ⟨(0, n), rfl⟩
  · intro ⟨m, n⟩
    simp only [LinearMap.snd_apply]
    constructor
    · intro hn
      exact ⟨m, by simp [hn]⟩
    · rintro ⟨x, hx⟩
      exact (congrArg Prod.snd hx).symm
  · exact powerTorsion_prod hM hN

lemma value_linearEquiv {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (hN : powerTorsion I (ModuleCat.of R N)) :
    ℓ.value (ModuleCat.of R M) = ℓ.value (ModuleCat.of R N) := by
  let e' := e.toModuleIso
  exact ℓ.eq_of_iso e' ((powerTorsion I).prop_of_iso e'.symm hN) hN

lemma value_fin {M : Type u} [AddCommGroup M] [Module R M]
    (hM : powerTorsion I (ModuleCat.of R M)) (n : ℕ) :
    ℓ.value (ModuleCat.of R (Fin n → M)) = n • ℓ.value (ModuleCat.of R M) := by
  induction n with
  | zero =>
    rw [ℓ.zero (ModuleCat.isZero_iff_subsingleton.mpr inferInstance), zero_nsmul]
  | succ n ih =>
    let e : (Fin (n + 1) → M) ≃ₗ[R] M × (Fin n → M) :=
      (LinearEquiv.piCongrLeft R (fun _ : Option (Fin n) => M) (finSuccEquiv n)) ≪≫ₗ
        LinearEquiv.piOptionEquivProd R
    rw [ℓ.value_linearEquiv e (powerTorsion_prod hM (powerTorsion_fin _ hM)),
      ℓ.value_prod hM (powerTorsion_fin _ hM), ih, succ_nsmul, add_comm]

end TorsionLength
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
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteFreeTensorCohomology
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.algebra _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Homogeneous.module _root_.OAI.Lech.Homogeneous.scalarTower _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.TensorIdeal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (P M : ModuleCat.{u} R) (b : ℕ)
  (B : Module.Basis (Fin b) R P)

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c)
  [Module.Flat R P]

variable (I : Ideal R) (ell : TorsionLength I)
include B in
lemma tensorHomology_torsion (q : ι) (ht : powerTorsion I (K.homology q)) :
    powerTorsion I
      (((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q) :=
  (powerTorsion I).prop_of_iso (tensorHomologyBasisIso P b B K q).symm
    (powerTorsion_fin b ht)

include B in
lemma tensorHomology_length (q : ι) (ht : powerTorsion I (K.homology q)) :
    ell.value
      (((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q) =
        b • ell.value (K.homology q) :=
  (ell.eq_of_iso (tensorHomologyBasisIso P b B K q)
    (tensorHomology_torsion P b B K I q ht) (powerTorsion_fin b ht)).trans
      (ell.value_fin ht b)

include B in
lemma tensorHomology_length_finite (q : ι) (ht : powerTorsion I (K.homology q))
    (hf : ell.value (K.homology q)≠⊤) :
    ell.value
      (((((curriedTensor (ModuleCat.{u} R)).obj P).mapHomologicalComplex c).obj K).homology q)≠⊤ := by
  rw [tensorHomology_length P b B K I ell q ht,nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) hf
end Lech.TensorIdeal

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

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootLayerCech
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.ReesRoot.coefficientAlgebra _root_.OAI.Lech.ReesRoot.coefficientTower _root_.OAI.Lech.ReesRoot.exceptionalAlgebra _root_.OAI.Lech.ReesRoot.exceptionalTower _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
variable (m : Fin n → ℤ)

variable (hgen : Ideal.span (Set.range z)=I)

attribute [local instance] OAI.Lech.ReesRoot.baseAlgebra_p9
attribute [local instance] OAI.Lech.ReesRoot.baseModule_p7
attribute [local instance] OAI.Lech.ReesRoot.concreteRing_p9
private local instance projectiveModule_rede5a8_1 (s : Finset (Fin (n+1))) :
    Module (ProjectiveRoot.Ring R n s) (Ring I z hz s) := (projectiveAlgebra I z hz s).toModule
attribute [local instance] OAI.Lech.ReesRoot.scalarComm_p6
attribute [local instance] OAI.Lech.ReesRoot.sectionGroup_p8
private local instance sectionBaseModule_rede5a8_1 (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module R (Sections I z hz s hs m) := TensorProduct.leftModule
attribute [local instance] OAI.Lech.ReesRoot.nonemptyFinite
include hgen in
lemma layerDiagram_shortExact (s : Finset (Fin (n+1))) :
    (FiniteModuleCech.diagramShortComplex (cechInclusionDiagram I z hz m)
      (layerProjection I z hz m) (layerDiagram_zero I z hz m hgen) s).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr (by
    intro x y hxy
    funext hs
    exact inclusion_injective I z hz s hs.down m (congrFun hxy hs))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)
  exact := (ShortComplex.moduleCat_exact_iff _).mpr (by
    intro y hy
    change Submodule.Quotient.mk y=0 at hy
    have hys := (TensorIdeal.mem_smul_pi_iff I
      (fun hs : PLift s.Nonempty => Sections I z hz s hs.down m) y).mp
      ((Submodule.Quotient.mk_eq_zero _).mp hy)
    have hyr (hs : PLift s.Nonempty) : y hs ∈ (inclusion I z hz s hs.down m).range := by
      rw [inclusion_range I z hz s hs.down m hgen]
      exact hys hs
    choose x hx using fun hs : PLift s.Nonempty => hyr hs
    exact ⟨x,funext hx⟩)

end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorCechRankEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.FiniteModuleCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)
  {ι : Type} [Fintype ι] [LinearOrder ι]
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (D : Diagram R ι) (hf : ∀ q,ell.finiteClass ((positiveZ D).homology q))

include B hflat hb hf in
lemma tensorCech_finite_of_positive (i : ℤ) : ell.finiteClass ((tensorCech F D).homology i) := by
  apply BicomplexTotal.devissage ell.finiteClass (-(h:ℤ)) (h+1) _ i
  · intro p hp
    apply FiniteComplex.isZero_of_X
    intro q
    exact (tensorRight ((positiveZ D).X q)).map_isZero (hb p (by omega))
  intro p
  apply ell.finiteClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p i).symm
  let := hflat p
  exact ⟨TensorIdeal.tensorHomology_torsion (F.X p) (b p) (B p) (positiveZ D) I _ (hf _).1,
    TensorIdeal.tensorHomology_length_finite (F.X p) (b p) (B p) (positiveZ D) I ell _ (hf _).1 (hf _).2⟩

end Lech.FiniteModuleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootEulerConstant
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
  [LinearOrder (Chart n)]
  (hgen : Ideal.span (Set.range z)=I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)
  (hbr : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)=0)

include hgen hds hmu ha B hflat hp hfin hb hac hbr in
lemma unfilteredEuler_diagonal_oai (m : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h (fun i => m i+1)=unfilteredEuler I z hz ell F h m := by
  have hE (q : ℤ) : ell.finiteClass ((positiveZ (exceptionalDiagram I z hz m)).homology q) :=
    exceptionalZ_finite I z hz m hgen ell hds hmu ha q
  have he := tensorEuler_additive (cechInclusionDiagram I z hz m) (layerProjection I z hz m)
    (layerDiagram_zero I z hz m hgen) ell F h hb hflat
    (layerDiagram_shortExact I z hz m hgen)
    (unfilteredTotal_finite I z hz F h _ hgen ell hds hmu ha b B hflat hp hfin hb hac)
    (tensorCech_finite_of_positive ell F h b B hflat hb (exceptionalDiagram I z hz m) hE)
  have hzE := tensor_euler_rank_zero ell F h b B hflat hb (exceptionalDiagram I z hz m) hE hbr
  change unfilteredEuler I z hz ell F h m=unfilteredEuler I z hz ell F h (fun i => m i+1)+
    tensorEuler ell F h (exceptionalDiagram I z hz m) at he
  rw [hzE,add_zero] at he
  exact he.symm

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.unfilteredEuler_diagonal_oai.{u} := @OAI.Lech.ReesRoot.unfilteredEuler_diagonal_oai.{u}
