-- Prove2me | solution 1 for OAI.Lech.frobenius_shortComplex_homology_finiteLength
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:08:49.774606+00:00
-- url     : https://prove2.me/submissions/f75a9b03-23ae-4510-af6a-71c8bb7bb5a0

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator

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
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteModuleTensor
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
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
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_ProjectiveGhost
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex
namespace Lech.ProjectiveGhost
universe u
variable {R : Type u} [CommRing R]

lemma scalar_cycle_boundary (S : ShortComplex (ModuleCat.{u} R)) (x : R)
    (hx : ∀ z : S.homology, x • z = 0) (y : S.X₂) (hy : S.g y = 0) :
    ∃ z : S.X₁, S.f z = x • y := by
  let c : LinearMap.ker S.g.hom := ⟨y,hy⟩
  let Q := LinearMap.range S.moduleCatToCycles
  let q : (LinearMap.ker S.g.hom) ⧸ Q := Q.mkQ c
  have hq : x • q = 0 := by
    let e := S.moduleCatHomologyIso.toLinearEquiv
    have h := congrArg e (hx (e.symm q))
    have hz := (e.map_smul x (e.symm q)).symm.trans (h.trans e.map_zero)
    exact (congrArg (fun z => x • z) (e.apply_symm_apply q)).symm.trans hz
  have hc : x • c ∈ Q := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact (map_smul Q.mkQ x c).trans hq
  obtain ⟨z,hz⟩ := hc
  exact ⟨z,congrArg Subtype.val hz⟩

 

lemma correct (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (j : ℤ) [Module.Projective R (F.X j)]
    (hx : ∀ z : F.homology j, x • z = 0)
    (f : F ⟶ F) (hf : ∀ i, j < i → f.f i = 0) :
    ∃ f' : F ⟶ F, Nonempty (Homotopy (x • f) f') ∧
      ∀ i, j ≤ i → f'.f i = 0 := by
  have hcycles (v : F.X j) : (F.d j (j+1)) (f.f j v) = 0 := by
    have h := congrArg (fun g : F.X j ⟶ F.X (j+1) => g v) (f.comm j (j+1))
    rw [hf (j+1) (by omega)] at h
    rw [comp_zero] at h
    exact h
  have hmem (v : F.X j) : x • f.f j v ∈ LinearMap.range (F.d (j-1) j).hom := by
    let e := F.homologyIsoSc' (j-1) j (j+1) (by simp) (by simp)
    have hx' (z : (F.sc' (j-1) j (j+1)).homology) : x • z = 0 := by
      let l := e.toLinearEquiv
      calc
        x • z = l (x • l.symm z) := by rw [l.map_smul,l.apply_symm_apply]
        _ = l 0 := congrArg l (hx (l.symm z))
        _ = 0 := l.map_zero
    obtain ⟨w,hw⟩ := scalar_cycle_boundary (F.sc' (j-1) j (j+1)) x hx'
      (f.f j v) (hcycles v)
    exact ⟨w,hw⟩
  let a : F.X j →ₗ[R] LinearMap.range (F.d (j-1) j).hom :=
    (x • (f.f j).hom).codRestrict _ hmem
  obtain ⟨h,hh⟩ := Module.projective_lifting_property
    (F.d (j-1) j).hom.rangeRestrict a (F.d (j-1) j).hom.surjective_rangeRestrict
  have hh' : ModuleCat.ofHom h ≫ F.d (j-1) j = x • f.f j := by
    apply ModuleCat.hom_ext
    ext v
    exact congrArg Subtype.val (LinearMap.congr_fun hh v)
  let α : Cochain F F (-1) := Cochain.single (ModuleCat.ofHom h) (-1)
  let b : F ⟶ F := (Cocycle.mk (δ (-1) 0 α) 1 (by norm_num) (δ_δ _ _ _ _)).homOf
  have hb : Cochain.ofHom b = δ (-1) 0 α := Cocycle.cochain_ofHom_homOf_eq_coe _
  have hb0 : Homotopy b 0 := (Cochain.equivHomotopy b 0).symm ⟨α, by simpa using hb⟩
  refine ⟨x • f - b, ⟨?_⟩, ?_⟩
  · simpa [sub_eq_add_neg] using ((Homotopy.refl (x • f)).add (hb0.smul (-1:R))).symm
  · intro i hi
    have hbval := Cochain.congr_v hb i i (by omega)
    rw [δ_v (-1) 0 (by norm_num) α i i (by omega) (i-1) (i+1) (by omega) (by omega)] at hbval
    have hz : (Cochain.single (ModuleCat.ofHom h) (-1)).v (i+1) i (by omega) = 0 :=
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)
    by_cases he : i=j
    · subst i
      simp only [α,Cochain.single_v,hz,comp_zero,smul_zero,add_zero,
        Cochain.ofHom_v] at hbval
      simp [hbval,hh']
    · have hz' : (Cochain.single (ModuleCat.ofHom h) (-1)).v i (i-1) (by omega) = 0 :=
        Cochain.single_v_eq_zero _ _ _ _ _ he
      simp only [α,hz,hz',zero_comp,comp_zero,smul_zero,add_zero,
        Cochain.ofHom_v] at hbval
      simp [hf i (by omega),hbval]
 

theorem nullhomotopy_pow (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (m : ℤ) (N : ℕ) (hp : ∀ i, Module.Projective R (F.X i))
    (hb : ∀ i, i < m ∨ m+N ≤ i → IsZero (F.X i))
    (x : R) (hx : ∀ i (z : F.homology i), x • z = 0) :
    Nonempty (Homotopy (x^N • 𝟙 F) 0) := by
  have (i : ℤ) : Module.Projective R (F.X i) := hp i
  have hstep (n : ℕ) : ∃ f : F ⟶ F, Nonempty (Homotopy (x^n • 𝟙 F) f) ∧
      ∀ i, m+N-(n:ℤ) ≤ i → f.f i = 0 := by
    induction n with
    | zero =>
      refine ⟨𝟙 F,⟨by simpa using Homotopy.refl (𝟙 F)⟩,?_⟩
      intro i hi
      exact (hb i (Or.inr (by simpa using hi))).eq_of_src _ _
    | succ n ih =>
      obtain ⟨f,⟨H⟩,hf⟩ := ih
      obtain ⟨f',⟨H'⟩,hf'⟩ := correct F x (m+N-n-1) (hx _) f
        (fun i hi => hf i (by omega))
      refine ⟨f',⟨?_⟩,fun i hi => hf' i (by omega)⟩
      simpa [smul_smul,pow_succ,mul_comm] using (H.smul x).trans H'
  obtain ⟨f,⟨H⟩,hf⟩ := hstep N
  have he : f=0 := by
    ext i : 1
    by_cases hi : i < m
    · exact (hb i (Or.inl hi)).eq_of_src _ _
    · exact hf i (by omega)
  exact ⟨H.trans (Homotopy.ofEq he)⟩
 

theorem exists_nullhomotopy_power [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ)
    (hp : ∀ i, Module.Projective R (F.X i))
    (hb : ∀ i, i < m ∨ m+N ≤ i → IsZero (F.X i))
    (hH : ∀ i, IsFiniteLength R (F.homology i))
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, Nonempty (Homotopy (x^a • 𝟙 F) 0) := by
  classical
  let M := ∀ i : Fin N,F.homology (m+i)
  have (i : Fin N) : IsNoetherian R (F.homology (m+i)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hH _)).1
  have (i : Fin N) : IsArtinian R (F.homology (m+i)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (hH _)).2
  have hM : IsFiniteLength R M :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance,inferInstance⟩
  obtain ⟨I,hIr,hI⟩ := Lech.finiteLength_primary_annihilator hM
  obtain ⟨a,ha⟩ := Ideal.mem_radical_iff.mp (show x ∈ I.radical from hIr.symm ▸ hx)
  have hkill (i : ℤ) (z : F.homology i) : x^a • z = 0 := by
    by_cases hi : i < m ∨ m+N ≤ i
    · have hz := ExactAt.isZero_homology (ExactAt.of_isZero (hb i hi))
      have := ModuleCat.isZero_iff_subsingleton.mp hz
      exact Subsingleton.elim _ _
    · obtain ⟨j,rfl⟩ : ∃ j : Fin N,m+j=i :=
        ⟨⟨(i-m).toNat,by omega⟩,by change m + ((i-m).toNat:ℤ) = i; omega⟩
      have hz := Module.mem_annihilator.mp (hI ha) (Pi.single j z)
      have hz' := congrFun hz j
      change x^a • ((Pi.single j z : M) j) = 0 at hz'
      simpa only [Pi.single_eq_same] using hz' 
  refine ⟨a*N,?_⟩
  simpa only [pow_mul] using nullhomotopy_pow F m N hp hb (x^a) hkill
end Lech.ProjectiveGhost

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusHomologyFinite
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

 
theorem frobenius_shortComplex_homology_finiteLength_oai
    [IsLocalRing R] [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) (n : ℕ) (i : ℤ) :
    IsFiniteLength R ((frobeniusComplex R p n F).homology i) := by
  have := hF.term_finite i
  have : Module.Finite R ((frobeniusComplex R p n F).X i) :=
    finite_extendScalars (iterateFrobenius R p n) (F.X i)
  have := finite_cochain_homology (frobeniusComplex R p n F) i
  apply finiteLength_of_maximal_le_radical_annihilator
  intro x hx
  obtain ⟨a,ha⟩ := ProjectiveGhost.exists_nullhomotopy_power F
    (-(dimension R : ℤ)) (dimension R+1)
    (fun j => by have := hF.term_free j; infer_instance)
    (fun j hj => hF.bounded j (by omega)) hF.homology_finite_length x hx
  refine ⟨a*(p^n),?_⟩
  exact Koszul.scalar_annihilates_homology (frobeniusComplex R p n F) (x^(a*(p^n)))
    (frobenius_nullhomotopy p n a F x ha.some) i
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.frobenius_shortComplex_homology_finiteLength_oai.{u} := @OAI.Lech.frobenius_shortComplex_homology_finiteLength_oai.{u}
