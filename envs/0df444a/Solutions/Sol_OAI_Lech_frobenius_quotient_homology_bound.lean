-- Prove2me | solution 1 for OAI.Lech.frobenius_quotient_homology_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:07:18.709224+00:00
-- url     : https://prove2.me/submissions/8976254c-7921-48bd-8928-f53caeb13779

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_Koszul_length_quotient_tensor_le_sum
import Theorems.Thm_OAI_Lech_shortComplex_nullScalar_radical

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulHomologyMap
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex


namespace Lech.Koszul
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
universe u v
variable {R : Type u} [CommRing R]


lemma inclusion_homology_injective
    (F : CochainComplex (ModuleCat.{v} R) ℤ)
    (zs : List R) (H : ∀ r ∈ zs, Homotopy (r • 𝟙 F) 0) (i : ℤ) :
    Function.Injective (HomologicalComplex.homologyMap (inclusion F zs) i) := by
  have he := congrArg (fun f => HomologicalComplex.homologyMap f i)
    (inclusion_retraction F zs H)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at he
  intro x y hxy
  have hx := congrArg (fun f => f x) he
  have hy := congrArg (fun f => f y) he
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hx hy
  rw [← hx, ← hy, hxy]


end Lech.Koszul
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

lemma length_le_add_of_exact {R M N P : Type*} [Ring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    (f : N →ₗ[R] M) (g : M →ₗ[R] P) (hg : Function.Surjective g)
    (he : Function.Exact f g) :
    Module.length R M ≤ Module.length R N + Module.length R P := by
  let f' : N →ₗ[R] g.ker := f.codRestrict g.ker (fun n => by
    rw [LinearMap.exact_iff.mp he]
    exact ⟨n, rfl⟩)
  have hf' : Function.Surjective f' := by
    rintro ⟨m, hm⟩
    rw [LinearMap.exact_iff.mp he] at hm
    obtain ⟨n, rfl⟩ := hm
    exact ⟨n, rfl⟩
  rw [Module.length_eq_add_of_exact g.ker.subtype g g.ker.subtype_injective hg
    (LinearMap.exact_subtype_ker_map g)]
  exact add_le_add (Module.length_le_of_surjective f' hf') le_rfl

end Lech


open scoped BigOperators
end
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



lemma shortComplex_uniform_nullhomotopy [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    ∃ a : ℕ, 0 < a ∧ (IsLocalRing.maximalIdeal R)^a ≤ Koszul.nullScalarIdeal F := by
  obtain ⟨a,ha⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (shortComplex_nullScalar_radical F hF)
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  exact ⟨a+1,by omega,(Ideal.pow_le_pow_right (Nat.le_succ a)).trans ha⟩

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulPowerGrowth
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

lemma length_le_sum_of_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) :
    Module.length R S.X₂ ≤ Module.length R S.X₁ + Module.length R S.X₃ := by
  have he : Function.Exact S.f.hom S.g.hom := by
    rw [LinearMap.exact_iff]
    ext x
    constructor
    · exact S.moduleCat_exact_iff.mp hS x
    · rintro ⟨y,rfl⟩
      exact congrArg (fun f : S.X₁ ⟶ S.X₃ => f y) S.zero
  have he' : Function.Exact S.f.hom S.g.hom.rangeRestrict := by
    rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, LinearMap.exact_iff.mp he]
  exact (Lech.length_le_add_of_exact S.f.hom S.g.hom.rangeRestrict
    S.g.hom.surjective_rangeRestrict he').trans
    (add_le_add le_rfl (Module.length_le_of_injective S.g.hom.range.subtype
      S.g.hom.range.subtype_injective))

lemma length_cone_comp_le {F G H : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : F ⟶ G) (g : G ⟶ H) (i : ℤ) :
    Module.length R ((mappingCone (f ≫ g)).homology i) ≤
      Module.length R ((mappingCone f).homology i) +
      Module.length R ((mappingCone g).homology i) := by
  let Q := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  let T := mappingConeCompTriangleh f g
  have hT := HomotopyCategory.mappingConeCompTriangleh_distinguished f g
  have hex := Q.map_distinguished_exact T hT
  have hl := length_le_sum_of_exact _ hex
  let e := HomotopyCategory.homologyFunctorFactors (ModuleCat.{u} R) (.up ℤ) i
  have he (E : CochainComplex (ModuleCat.{u} R) ℤ) :
      Module.length R (Q.obj ((HomotopyCategory.quotient _ _).obj E)) =
        Module.length R (E.homology i) := (e.app E).toLinearEquiv.length_eq
  change Module.length R (Q.obj T.obj₂) ≤
    Module.length R (Q.obj T.obj₁) + Module.length R (Q.obj T.obj₃) at hl
  rw [← he (mappingCone (f ≫ g)), ← he (mappingCone f), ← he (mappingCone g)]
  exact hl

lemma length_cone_pow_le (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (n : ℕ) (i : ℤ) :
    Module.length R ((mappingCone (x^n • 𝟙 F)).homology i) ≤
      n • Module.length R ((mappingCone (x • 𝟙 F)).homology i) := by
  induction n with
  | zero =>
    have he : mappingCone (x^0 • 𝟙 F) ≅ mappingCone (𝟙 F) :=
      eqToIso (congrArg (fun f : F ⟶ F => mappingCone f) (by simp))
    have hl : Module.length R ((mappingCone (x^0 • 𝟙 F)).homology i) =
        Module.length R ((mappingCone (𝟙 F)).homology i) :=
      ((homologyFunctor _ _ i).mapIso he).toLinearEquiv.length_eq
    rw [hl,zero_nsmul,le_zero_iff]
    apply Module.length_eq_zero_iff.mpr
    apply ModuleCat.isZero_iff_subsingleton.mp
    apply (IsZero.iff_id_eq_zero _).mpr
    simpa using (mappingCone.homotopyToZeroOfId F).homologyMap_eq i
  | succ n ih =>
    have he : x^(n+1) • 𝟙 F = (x^n • 𝟙 F) ≫ (x • 𝟙 F) := by
      simp [pow_succ,Linear.comp_smul,smul_smul,mul_comm]
    rw [he,add_nsmul,one_nsmul]
    exact (length_cone_comp_le _ _ i).trans (add_le_add ih le_rfl)

 

lemma length_tensor_powers_le (zs : List R) (q : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module.length R ((tensor (zs.map (fun z => z^q)) F).homology i) ≤
      (q^zs.length) • Module.length R ((tensor zs F).homology i) := by
  induction zs generalizing F with
  | nil =>
    change Module.length R (F.homology i) ≤ 1 • Module.length R (F.homology i)
    simp
  | cons a zs ih =>
    simp only [tensor_cons,List.length_cons,pow_succ]
    have h₁ := length_cone_pow_le (tensor (zs.map (fun z => z^q)) F) a q i
    have h₂ := ih (scalarCone a F)
    have he (ys : List R) :
        Module.length R ((scalarCone a (tensor ys F)).homology i) =
          Module.length R ((tensor ys (scalarCone a F)).homology i) :=
      ((homologyFunctor _ _ i).mapIso (tensorConeIso ys a F)).toLinearEquiv.length_eq
    rw [← he zs, ← he (zs.map (fun z => z^q))] at h₂
    calc
      _ ≤ q • Module.length R ((scalarCone a (tensor (zs.map (fun z => z^q)) F)).homology i) := h₁
      _ ≤ q • ((q^zs.length) • Module.length R ((scalarCone a (tensor zs F)).homology i)) :=
        nsmul_le_nsmul_right h₂ q
      _ = _ := by
        rw [smul_smul, Nat.mul_comm]
        rfl

end Lech.Koszul

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulFiniteComplexBound
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]



theorem length_quotient_le_koszul_powers (I : Ideal R) (zs : List R) (q : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j))
    (hfree : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (H : ∀ r∈zs, Homotopy
      (r^q • 𝟙 ((complexQuotient I (.up ℤ)).obj F)) 0) :
    Module.length R (((complexQuotient I (.up ℤ)).obj F).homology i) ≤
      (q^zs.length) • ∑ k∈Finset.range N,
        Module.finrank R (F.X (m+k)) • Module.length R
          ((tensor zs ((complexQuotient I (.up ℤ)).obj
            ((single (ModuleCat R) (.up ℤ) (m+k)).obj (ModuleCat.of R R)))).homology i) := by
  let G := (complexQuotient I (.up ℤ)).obj F
  have H' (r : R) (hr : r∈zs.map (fun x => x^q)) : Homotopy (r • 𝟙 G) 0 := by
    apply Classical.choice
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact ⟨H x hx⟩
  exact (Module.length_le_of_injective (homologyMap (inclusion G _) i).hom
    (inclusion_homology_injective G _ H' i)).trans
      ((length_tensor_powers_le zs q G i).trans
        (nsmul_le_nsmul_right (length_quotient_tensor_le_sum I zs F m N i hb hfree hfin) _))
end Lech.Koszul

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

lemma finrank_extendScalars [Nontrivial R] [Nontrivial S]
    (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.finrank S ((ModuleCat.extendScalars φ).obj M) = Module.finrank R M := by
  let := φ.toAlgebra
  change Module.finrank S (S ⊗[R] M) = Module.finrank R M
  exact Module.finrank_baseChange



theorem frobenius_quotient_homology_bound_oai [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (I : Ideal R) (zs : List R) (hzs : ∀ z∈zs,z∈IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, 0 < a ∧ ∀ n i,
      Module.length R (((complexQuotient I (.up ℤ)).obj (frobeniusComplex R p n F)).homology i) ≤
        ((p^n)^zs.length) • ∑ k∈Finset.range (dimension R+1),
          Module.finrank R (F.X (-(dimension R : ℤ)+k)) • Module.length R
            ((Koszul.tensor (zs.map (fun z => z^a)) ((complexQuotient I (.up ℤ)).obj
              ((single (ModuleCat R) (.up ℤ) (-(dimension R : ℤ)+k)).obj
                (ModuleCat.of R R)))).homology i) := by
  obtain ⟨a,ha,haF⟩ := shortComplex_uniform_nullhomotopy F hF
  refine ⟨a,ha,fun n i => ?_⟩
  let G := frobeniusComplex R p n F
  have hfree (j : ℤ) : Module.Free R (G.X j) := by
    have := hF.term_free j
    exact free_extendScalars (iterateFrobenius R p n) (F.X j)
  have hfin (j : ℤ) : Module.Finite R (G.X j) := by
    have := hF.term_finite j
    exact finite_extendScalars (iterateFrobenius R p n) (F.X j)
  have hb (j : ℤ) (hj : j < -(dimension R:ℤ) ∨ -(dimension R:ℤ)+(dimension R+1) ≤ j) :
      IsZero (G.X j) :=
    (ModuleCat.extendScalars (iterateFrobenius R p n)).map_isZero
      (hF.bounded j (by omega))
  have H (r : R) (hr : r∈zs.map (fun z => z^a)) :
      Homotopy (r^(p^n) • 𝟙 ((complexQuotient I (.up ℤ)).obj G)) 0 := by
    apply Classical.choice
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    have Hz := (haF (Ideal.pow_mem_pow (hzs z hz) a)).some
    refine ⟨?_⟩
    simpa only [pow_mul] using Koszul.quotient_nullhomotopy I G _
      (frobenius_nullhomotopy p n a F z Hz)
  have hl := Koszul.length_quotient_le_koszul_powers I (zs.map (fun z => z^a)) (p^n)
    G (-(dimension R:ℤ)) (dimension R+1) i hb hfree hfin H
  have hrank (j : ℤ) : Module.finrank R (G.X j) = Module.finrank R (F.X j) := by
    have := hF.term_free j
    exact finrank_extendScalars (iterateFrobenius R p n) (F.X j)
  simpa only [List.length_map,hrank] using hl
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.frobenius_quotient_homology_bound_oai.{u} := @OAI.Lech.frobenius_quotient_homology_bound_oai.{u}
