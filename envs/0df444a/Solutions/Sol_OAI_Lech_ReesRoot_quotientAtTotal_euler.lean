-- Prove2me | solution 1 for OAI.Lech.ReesRoot.quotientAtTotal_euler
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T23:22:51.941797+00:00
-- url     : https://prove2.me/submissions/d7e01409-2888-4b5f-b42d-67823316b493

import Mathlib
import Definitions.Def_OAIQ032L037
import Definitions.Def_OAIQ032L038
import Theorems.Thm_OAI_Lech_ReesRoot_thickeningZ_euler
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
lemma finiteHomologyEuler_zero (hK : ∀ q,IsZero (K.homology q)) (m : ℤ) (N : ℕ) :
    finiteHomologyEuler ℓ K m N=0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [ℓ.realValue_zero (hK _),mul_zero]
end Lech


namespace Lech.FiniteComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u v
variable {R : Type u} [CommRing R] {I : Ideal R} (ℓ : TorsionLength I)
variable {C : Type v} [Category C] [Abelian C]
variable (T : CochainComplex C ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ) [T.Additive]
variable (hT : ∀ (S : ShortComplex (CochainComplex C ℤ)),
  (∀ j, (S.map (eval C (.up ℤ) j)).Splitting) →
  ∀ j, ((S.map T).map (eval (ModuleCat.{u} R) (.up ℤ) j)).Splitting)
variable (a : ℤ) (w : ℕ)
include hT in
 

theorem euler_devissage (m : ℤ) (N : ℕ) (F : CochainComplex C ℤ)
    (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j))
    (hf : ∀ j q, ℓ.finiteClass ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology q))
    (hl : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology (a-1)))
    (hr : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology (a+w+1))) :
    finiteHomologyEuler ℓ (T.obj F) a w =
      ∑ k ∈ Finset.range N,finiteHomologyEuler ℓ (T.obj
        ((single C (.up ℤ) (m+k)).obj (F.X (m+k)))) a w := by
  induction N generalizing F with
  | zero =>
    rw [Finset.range_zero,Finset.sum_empty]
    apply finiteHomologyEuler_zero
    intro q
    exact (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero
      (T.map_isZero (isZero_of_X F (fun j => hb j (by omega))))
  | succ N ih =>
    let n : ℤ := m+N
    have hn : ∀ j,n<j → IsZero (F.X j) := fun j hj => hb j (by dsimp [n] at hj;omega)
    let D := dropTop F n hn
    have hbD : ∀ j,j < m ∨ m+(N:ℤ)≤j → IsZero (D.X j) := by
      intro j hj
      by_cases hjn : j=n
      · subst j;exact dropTop_X_top F n hn
      · exact (hb j (by dsimp [n] at hjn;omega)).of_iso (dropTopXIso F n hn j hjn).symm
    have hpiece (P : ObjectProperty (ModuleCat.{u} R)) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
        (q : ℤ) (h : ∀ j,P ((T.obj ((single C (.up ℤ) j).obj (F.X j))).homology q))
        (j : ℤ) : P ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology q) := by
      by_cases hjn : j=n
      · subst j
        exact P.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).map_isZero
          (T.map_isZero ((single C (.up ℤ) n).map_isZero (dropTop_X_top F n hn))))
      · exact P.prop_of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
          (T.mapIso ((single C (.up ℤ) j).mapIso (dropTopXIso F n hn j hjn)))) (h j)
    have hfD : ∀ j q,ℓ.finiteClass ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology q) :=
      fun j q => hpiece ℓ.finiteClass q (fun t => hf t q) j
    have hlD : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology (a-1)) :=
      hpiece (IsZero (C:=ModuleCat.{u} R)) (a-1) hl
    have hrD : ∀ j,IsZero ((T.obj ((single C (.up ℤ) j).obj (D.X j))).homology (a+w+1)) :=
      hpiece (IsZero (C:=ModuleCat.{u} R)) (a+w+1) hr
    have hfiniteF (q : ℤ) : ℓ.finiteClass ((T.obj F).homology q) :=
      homology_devissage_to ℓ.finiteClass T hT m (N+1) F q hb (fun j => hf j q)
    have hfiniteD (q : ℤ) : ℓ.finiteClass ((T.obj D).homology q) :=
      homology_devissage_to ℓ.finiteClass T hT m N D q hbD (fun j => hfD j q)
    have hleftD : IsZero ((T.obj D).homology (a-1)) :=
      homology_devissage_to (IsZero (C:=ModuleCat.{u} R)) T hT m N D (a-1) hbD hlD
    have hs : ((topShortComplex F n hn).map T).ShortExact :=
      shortExact_of_degreewise_shortExact _ (fun j => (hT _ (topSplitting F n hn) j).shortExact)
    have he := finiteHomologyEuler_additive ℓ ((topShortComplex F n hn).map T) hs a w
      (hf n) hfiniteF hfiniteD hleftD (hr n)
    change finiteHomologyEuler ℓ (T.obj F) a w =
      finiteHomologyEuler ℓ (T.obj ((single C (.up ℤ) n).obj (F.X n))) a w+
        finiteHomologyEuler ℓ (T.obj D) a w at he
    rw [he,ih D hbD hfD hlD hrD,Finset.sum_range_succ,add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : m+(k:ℤ)≠n := by dsimp [n];have := Finset.mem_range.mp hk;omega
    apply (finiteHomologyEuler_iso ℓ _ _
      (T.mapIso ((single C (.up ℤ) (m+k)).mapIso (dropTopXIso F n hn (m+k) hkn)))
      (fun q => (hf (m+k) q).1) a w).symm
end Lech.FiniteComplex


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
-- module Solutions.OAIQ032_LECH.Multiplicity_BicomplexEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)

lemma finiteHomologyEuler_shifted_window (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n k N : ℕ) (hN : k+n≤N)
    (hz : ∀ q,q<0 ∨ (n:ℤ)<q → ell.realValue (K.homology q)=0) :
    finiteHomologyEuler ell K (-(k:ℤ)) N=(-1:ℝ)^k*finiteHomologyEuler ell K 0 n := by
  unfold finiteHomologyEuler
  rw [show N+1=k+(n+1)+(N-k-n) by omega,Finset.sum_range_add,Finset.sum_range_add]
  have hfirst : (∑ j∈Finset.range k,(-1:ℝ)^j*ell.realValue (K.homology (-(k:ℤ)+j)))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz _ (Or.inl (by have := Finset.mem_range.mp hj; omega)),mul_zero]
  have hlast : (∑ j∈Finset.range (N-k-n),(-1:ℝ)^(k+(n+1)+j)*
      ell.realValue (K.homology (-(k:ℤ)+(k+(n+1)+j:ℕ))))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz _ (Or.inr (by omega)),mul_zero]
  rw [hfirst,hlast,zero_add,add_zero,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_add]
  rw [mul_assoc]
  congr 2
  congr 1
  push_cast
  ring_nf

namespace BicomplexTotal

lemma single_euler (K : Row (R:=R)) (p a : ℤ) (w : ℕ)
    (ht : ∀ q,powerTorsion I (K.homology q)) :
    finiteHomologyEuler ell (total ((single (Row (R:=R)) (.up ℤ) p).obj K) (.up ℤ)) a w=
      finiteHomologyEuler ell K (a-p) w := by
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  have hp := (powerTorsion I).prop_of_iso (singleHomologyIso K p (a+k)).symm (ht (-p+(a+k)))
  have he := ell.eq_of_iso (singleHomologyIso K p (a+k)) hp (ht _)
  change (ell.value _).toReal=(ell.value _).toReal
  rw [he]
  have hi : -p+(a+(k:ℤ))=a-p+k := by ring
  rw [hi]

 

lemma euler_rows (K : Double (R:=R)) (h n N : ℕ) (hN : h+n≤N)
    (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (K.X p))
    (hq : ∀ p q,q<0 ∨ (n:ℤ)<q → IsZero ((K.X p).homology q))
    (hf : ∀ p q,ell.finiteClass ((K.X p).homology q)) :
    finiteHomologyEuler ell (total K (.up ℤ)) (-(h:ℤ)) N=
      ∑ k∈Finset.range (h+1),(-1:ℝ)^k*finiteHomologyEuler ell (K.X (-(h:ℤ)+k)) 0 n := by
  have he := FiniteComplex.euler_devissage ell functor (splitting) (-(h:ℤ)) N
    (-(h:ℤ)) (h+1) K (fun p hp => hb p (by omega))
    (fun p q => ell.finiteClass.prop_of_iso (singleHomologyIso (K.X p) p q).symm (hf p (-p+q)))
    (fun p => ?_) (fun p => ?_)
  · change finiteHomologyEuler ell (total K (.up ℤ)) _ _=_ at he
    rw [he]
    apply Finset.sum_congr rfl
    intro k hk
    change finiteHomologyEuler ell (total ((single (Row (R:=R)) (.up ℤ) (-(h:ℤ)+k)).obj (K.X (-(h:ℤ)+k))) (.up ℤ)) _ _=_
    rw [single_euler ell _ _ _ _ (fun q => (hf _ q).1)]
    have heq : -(h:ℤ)-(-(h:ℤ)+k)=-(k:ℤ) := by ring
    rw [heq]
    apply finiteHomologyEuler_shifted_window ell _ n k N (by have := Finset.mem_range.mp hk; omega)
    intro q hq'
    exact ell.realValue_zero (hq _ _ hq')
  · apply IsZero.of_iso _ (singleHomologyIso (K.X p) p _)
    by_cases hp : p < -(h:ℤ) ∨ 0<p
    · exact (homologyFunctor _ _ _).map_isZero (hb p hp)
    · exact hq p _ (Or.inl (by omega))
  · apply IsZero.of_iso _ (singleHomologyIso (K.X p) p _)
    by_cases hp : p < -(h:ℤ) ∨ 0<p
    · exact (homologyFunctor _ _ _).map_isZero (hb p hp)
    · exact hq p _ (Or.inr (by omega))
end BicomplexTotal
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootQuotient
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)


lemma quotientAt_isZero (p : ℤ) (hp : IsZero (F.X p)) :
    IsZero ((quotientAt I z hz F h s hd m).X p) := by
  apply FiniteComplex.isZero_of_X
  intro q
  let Q := (cechZ I z hz m).X q
  exact (TensorIdeal.quotientFunctor (I^(IdealFiltered.order h s p))).map_isZero
    ((tensorRight Q).map_isZero hp)

lemma quotientAt_row_bounded (p q : ℤ) (hq : q<0 ∨ (n:ℤ)<q) :
    IsZero (((quotientAt I z hz F h s hd m).X p).X q) := by
  have hzK : IsZero ((cechZ I z hz m).X q) :=
    FiniteModuleCech.positiveZ_bounded (cechDiagram I z hz m) q (by simpa using hq)
  exact (TensorIdeal.quotientFunctor (I^(IdealFiltered.order h s p))).map_isZero
    ((tensorLeft (F.X p)).map_isZero hzK)
end Lech.ReesRoot

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ReesRootQuotientEuler
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectDomain _root_.OAI.Lech.RootTower.perfectFractionAlgebra _root_.OAI.Lech.RootTower.perfectNormal _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (m : Fin n → ℤ)

variable (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))

variable [LinearOrder (Chart n)] (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))

include hgen hds hmu ha B hflat in
lemma quotientAt_row_finite (p q : ℤ) :
    ell.finiteClass (((quotientAt I z hz F h s hd m).X p).homology q) := by
  let := hflat p
  let K := thickeningZ I z hz m (IdealFiltered.order h s p)
  have hf := thickeningZ_finite I z hz m hgen ell hds hmu ha (IdealFiltered.order h s p) q
  apply ell.finiteClass.prop_of_iso
    ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso (quotientAtRowIso I z hz F h s hd m p))
  exact ⟨TensorIdeal.tensorHomology_torsion (F.X p) (b p) (B p) K I q hf.1,
    TensorIdeal.tensorHomology_length_finite (F.X p) (b p) (B p) K I ell q hf.1 hf.2⟩

include hgen hds hmu ha B hflat in
lemma quotientAt_row_euler (p : ℤ) :
    finiteHomologyEuler ell ((quotientAt I z hz F h s hd m).X p) 0 n=
      (b p:ℝ)*∑ j∈Finset.range (IdealFiltered.order h s p),
        finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n := by
  let := hflat p
  let K := thickeningZ I z hz m (IdealFiltered.order h s p)
  have hf (q : ℤ) := thickeningZ_finite I z hz m hgen ell hds hmu ha (IdealFiltered.order h s p) q
  rw [←finiteHomologyEuler_iso ell _ _ (quotientAtRowIso I z hz F h s hd m p)
    (fun q => TensorIdeal.tensorHomology_torsion (F.X p) (b p) (B p) K I q (hf q).1) 0 n]
  rw [←thickeningZ_euler I z hz m hgen ell hds hmu ha (IdealFiltered.order h s p)]
  unfold finiteHomologyEuler
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have he := TensorIdeal.tensorHomology_length (F.X p) (b p) (B p) K I ell (0+j) (hf _).1
  change (-1:ℝ)^j*(ell.value _).toReal=_
  rw [he,nsmul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_natCast]
  dsimp only [TorsionLength.realValue]
  ring

include hb hgen hds hmu ha B hflat in
 
lemma quotientAtTotal_euler_oai (N : ℕ) (hN : h+n≤N) :
    finiteHomologyEuler ell ((quotientAt I z hz F h s hd m).total (.up ℤ)) (-(h:ℤ)) N=
      ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)*
        ∑ j∈Finset.range (IdealFiltered.order h s (-(h:ℤ)+k)),
          finiteHomologyEuler ell (exceptionalZ I z hz (raise m j)) 0 n := by
  rw [BicomplexTotal.euler_rows ell _ h n N hN
    (fun p hp => quotientAt_isZero I z hz F h s hd m p (hb p hp))
    (fun p q hq => ShortComplex.isZero_homology_of_isZero_X₂ _
      (quotientAt_row_bounded I z hz F h s hd m p q hq))
    (quotientAt_row_finite I z hz F h s hd m hgen ell hds hmu ha b B hflat)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [quotientAt_row_euler I z hz F h s hd m hgen ell hds hmu ha b B hflat,mul_assoc]

end Lech.ReesRoot

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.ReesRoot.quotientAtTotal_euler_oai.{u} := @OAI.Lech.ReesRoot.quotientAtTotal_euler_oai.{u}
