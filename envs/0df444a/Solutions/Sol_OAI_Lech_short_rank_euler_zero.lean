-- Prove2me | solution 1 for OAI.Lech.short_rank_euler_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:10:20.943641+00:00
-- url     : https://prove2.me/submissions/ace263f9-5b84-4f4d-8d6d-d21365142f7d

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L013
import Definitions.Def_OAIQ032L017
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_finiteLength_primary_annihilator

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominatorTheory
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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


lemma exact_euler_zero (ℓ : TorsionLength I)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (l : ℤ) (n : ℕ)
    (hex : ∀ i, F.ExactAt i) (hfin : ∀ i, ℓ.finiteClass (F.X i))
    (hl : IsZero (F.X (l - 1))) (hr : IsZero (F.X (l + n + 1))) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * ℓ.realValue (F.X (l + i)) = 0 := by
  let a (i : ℕ) := ℓ.realValue (image (F.d (l + i - 1) (l + i)))
  have hi (i : ℕ) : ℓ.realValue (F.X (l + i)) = a i + a (i + 1) := by
    let S := ShortComplex.mk (F.d (l + i - 1) (l + i))
      (F.d (l + i) (l + i + 1)) (F.d_comp_d _ _ _)
    have hS : S.Exact := (F.exactAt_iff' (l + i - 1) (l + i) (l + i + 1)
      (by simp) (by simp)).mp (hex (l + i))
    have h := ℓ.exact_real_image_sum S hS (hfin _)
    have imagesCongr (j j' k k' : ℤ) (hj : j = j') (hk : k = k') :
        ℓ.realValue (image (F.d j k)) = ℓ.realValue (image (F.d j' k')) := by
      subst j'; subst k'; rfl
    exact h.trans (congrArg (ℓ.realValue (image S.f) + ·)
      (imagesCongr _ _ _ _ (by omega) (by omega)))
  simp_rw [hi]
  rw [alternating_sum_pairs a n]
  have ha₀ : a 0 = 0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_epi (factorThruImage (F.d (l + 0 - 1) (l + 0)))
    simpa using hl
  have ha₁ : a (n + 1) = 0 := by
    apply ℓ.realValue_zero
    apply IsZero.of_mono (Limits.image.ι (F.d (l + (n + 1) - 1) (l + (n + 1))))
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hr
  rw [ha₀, ha₁, mul_zero, add_zero]

end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
end


open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusModule
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_SubalgebraStageFromBase
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_ProjectiveGhost
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.extendScalars_additive
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

lemma finrank_extendScalars [Nontrivial R] [Nontrivial S]
    (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.finrank S ((ModuleCat.extendScalars φ).obj M) = Module.finrank R M := by
  let := φ.toAlgebra
  change Module.finrank S (S ⊗[R] M) = Module.finrank R M
  exact Module.finrank_baseChange

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LocalContractibility
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R]

lemma acyclic_of_contractible {A : Type u} [CommRing A]
    (F : CochainComplex (ModuleCat.{u} A) ℤ) (H : Homotopy (𝟙 F) 0) : F.Acyclic := by
  intro i
  rw [F.exactAt_iff_isZero_homology i]
  apply ModuleCat.isZero_iff_subsingleton.mpr
  have he := H.homologyMap_eq i
  rw [homologyMap_id,homologyMap_zero] at he
  refine ⟨fun x y => ?_⟩
  have hx := ConcreteCategory.congr_hom he x
  have hy := ConcreteCategory.congr_hom he y
  exact hx.trans hy.symm



end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootStripComplement
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Homogeneous.awayAlgebra _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ProductSourceCover
open scoped BigOperators

lemma signed_reverse (h : ℕ) (b : ℤ → ℝ) (f : ℕ → ℝ) :
    (-1:ℝ)^h*(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*f (h-k))=
      ∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))*f i := by
  rw [Finset.mul_sum,←Finset.sum_range_reflect
    (fun i => (-1:ℝ)^i*b (-(i:ℤ))*f i) (h+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k≤h := by have := Finset.mem_range.mp hk; omega
  have he : h+1-1-k=h-k := by omega
  rw [he]
  have hp : -(h:ℤ)+(k:ℤ) = -((h-k:ℕ):ℤ) := by omega
  have hs : (-1:ℝ)^h*(-1:ℝ)^k=(-1:ℝ)^(h-k) := by
    conv_lhs => rw [show h=(h-k)+k by omega,pow_add]
    have hsq : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [←mul_pow]; norm_num
    rw [mul_assoc,hsq,mul_one]
  rw [hp,←mul_assoc,←mul_assoc,hs]

lemma rank_reverse_zero (h : ℕ) (b : ℤ → ℝ)
    (hb : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)=0) :
    ∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))=0 := by
  have he := signed_reverse h b (fun _=>1)
  simpa only [mul_one,hb,mul_zero] using he.symm

end Lech.ProductSourceCover

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ShortRankEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsDomain R] in
lemma maximalIdeal_ne_bot_of_dimension_pos [IsDomain R] (hd : 0 < dimension R) :
    IsLocalRing.maximalIdeal R ≠ ⊥ := by
  intro he
  have hf : IsField R := Ring.isField_iff_maximal_bot.mpr (he ▸ IsLocalRing.maximalIdeal.isMaximal R)
  let := hf.toField
  have hh := dimension_cast R
  simp only [ringKrullDim_eq_zero_of_field] at hh
  have : dimension R = 0 := by exact_mod_cast hh
  omega

lemma short_rank_euler_zero_oai (hd : 0 < dimension R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    ∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
      (Module.finrank R (F.X (-(i:ℤ))):ℝ) = 0 := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (maximalIdeal_ne_bot_of_dimension_pos hd)
  obtain ⟨a,ha⟩ := ProjectiveGhost.exists_nullhomotopy_power F
    (-(dimension R:ℤ)) (dimension R+1)
    (fun i => by have := hF.term_free i; infer_instance)
    (fun i hi => hF.bounded i (by omega)) hF.homology_finite_length x hx
  let K := FractionRing R
  let E := ModuleCat.extendScalars (algebraMap R K)
  let G := (E.mapHomologicalComplex (.up ℤ)).obj F
  have hz : algebraMap R K (x^a) ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr (pow_ne_zero _ hx0)
  have hc : Homotopy (𝟙 G) 0 := by
    have H := extendScalars_nullhomotopy (algebraMap R K) F (x^a) ha.some
    have H' := H.smul ((algebraMap R K (x^a))⁻¹)
    simpa only [smul_smul,inv_mul_cancel₀ hz,one_smul,smul_zero] using H'
  have hex := acyclic_of_contractible G hc
  let ell : TorsionLength (⊥ : Ideal K) := ordinaryLength ⊥
  have hval (j : ℤ) : ell.realValue (G.X j) = (Module.finrank R (F.X j):ℝ) := by
    have := hF.term_free j
    have := hF.term_finite j
    have : Module.Finite K (G.X j) := finite_extendScalars (algebraMap R K) (F.X j)
    dsimp [ell,TorsionLength.realValue,ordinaryLength]
    rw [Module.length_eq_finrank,ENat.toENNReal_coe,ENNReal.toReal_natCast]
    exact congrArg Nat.cast (finrank_extendScalars (algebraMap R K) (F.X j))
  have hfin (j : ℤ) : ell.finiteClass (G.X j) := by
    refine ⟨⟨1,by simp⟩,?_⟩
    have := hF.term_free j
    have := hF.term_finite j
    have : Module.Finite K (G.X j) := finite_extendScalars (algebraMap R K) (F.X j)
    change (Module.length K (G.X j)).toENNReal ≠ ⊤
    rw [Module.length_eq_finrank,ENat.toENNReal_coe]
    exact ENNReal.natCast_ne_top _
  have he := exact_euler_zero ell G (-(dimension R:ℤ)) (dimension R) hex hfin
    (E.map_isZero (hF.bounded _ (by left; omega)))
    (E.map_isZero (hF.bounded _ (by right; omega)))
  simp_rw [hval] at he
  exact ProductSourceCover.rank_reverse_zero (dimension R) (fun j => (Module.finrank R (F.X j):ℝ)) he
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.short_rank_euler_zero_oai.{u} := @OAI.Lech.short_rank_euler_zero_oai.{u}
