-- Prove2me | solution 1 for OAI.Lech.CharP.dutta_minimal_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:11:06.296088+00:00
-- url     : https://prove2.me/submissions/03d1229b-643a-42c2-a07e-6ef846c56662

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L018
import Theorems.Thm_OAI_Lech_CharP_exists_length_with_module_limit
import Theorems.Thm_OAI_Lech_CharP_perfection_complex_value
import Theorems.Thm_OAI_Lech_MinimalReduction_exists_minimal_reduction
import Theorems.Thm_OAI_Lech_complex_estimate_allModule
import Theorems.Thm_OAI_Lech_frobenius_shortComplex_homology_finiteLength
import Theorems.Thm_OAI_Lech_shortComplex_nullScalar_radical
import Theorems.Thm_OAI_Lech_short_rank_euler_zero

section
-- module Solutions.OAIQ032_LECH.Multiplicity_CoefficientFieldLocalSection
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory


namespace Lech.Normalization
open IsLocalRing Filter
open scoped Topology ENNReal
variable {k D : Type*} [Field k] [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D]

omit [Field k] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] in
lemma radical_span_powers {ι : Type*} (z : ι → D) (q : ℕ) (hq : q ≠ 0) :
    (Ideal.span (Set.range fun i => z i^q)).radical =
      (Ideal.span (Set.range z)).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.pow_mem_of_mem _ (Ideal.subset_span (Set.mem_range_self i)) q (Nat.pos_of_ne_zero hq)
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨q,Ideal.subset_span ⟨i,rfl⟩⟩

end Lech.Normalization


end
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
-- module Solutions.OAIQ032_LECH.Multiplicity_TowerRestrictedLength
attribute [-instance] _root_.OAI.Lech.extendScalars_additive
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
open CategoryTheory
attribute [local instance] Classical.propDecidable


namespace Lech.CharP
open Lech.Koszul IsLocalRing Filter
open scoped ENNReal Topology
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  {p : ℕ} [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]

omit [IsDomain D] [IsLocalRing D] [IsNoetherianRing D]
  [IsAdicComplete (maximalIdeal D) D] in
lemma entryIdeal_ofFn {h : ℕ} (z : Fin h → D) :
    entryIdeal (List.ofFn z) = Ideal.span (Set.range z) := by
  apply congrArg Ideal.span
  ext x
  simp only [Set.mem_ofPred_eq,List.mem_ofFn,Set.mem_range]

end Lech.CharP
end
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

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaFrobeniusShift
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
-- module Solutions.OAIQ032_LECH.Multiplicity_LocalContractibility
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.RootTower.perfectAlgebra _root_.OAI.Lech.RootTower.perfectBaseAlgebra _root_.OAI.Lech.RootTower.perfectOriginalAlgebra _root_.OAI.Lech.RootTower.powerSeriesCharP _root_.OAI.Lech.extendScalars_additive
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
-- module Solutions.OAIQ032_LECH.Multiplicity_ScalarExtensionDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma extendScalars_range_le (φ : R →+* S) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (I : Ideal R) (J : Ideal S)
    (hf : f.hom.range ≤ I • (⊤ : Submodule R N)) (hI : I.map φ ≤ J) :
    ((ModuleCat.extendScalars φ).map f).hom.range ≤
      J • (⊤ : Submodule S ((ModuleCat.extendScalars φ).obj N)) := by
  let := φ.toAlgebra
  let P : Submodule S (S ⊗[R] N) := J • ⊤
  have hgen (x : N) (hx : x ∈ I • (⊤ : Submodule R N)) : (1:S) ⊗ₜ[R] x ∈ P := by
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      rw [TensorProduct.tmul_smul]
      change φ r • ((1:S) ⊗ₜ[R] y) ∈ P
      exact Submodule.smul_mem_smul (hI (Ideal.mem_map_of_mem φ hr)) Submodule.mem_top
    · intro x y hx hy
      rw [TensorProduct.tmul_add]
      exact P.add_mem hx hy
  change (f.hom.baseChange S).range ≤ P
  rintro _ ⟨x,rfl⟩
  induction x using OAI.tensorInductionOn with
  | tmul s m =>
    change s ⊗ₜ[R] f m ∈ P
    have hh := P.smul_mem s (hgen (f m) (hf (LinearMap.mem_range_self f.hom m)))
    simpa only [TensorProduct.smul_tmul',smul_eq_mul,mul_one] using hh
  | add x y hx hy =>
    rw [map_add]
    exact P.add_mem hx hy

lemma frobenius_minimal_depth [IsLocalRing R] [IsNoetherianRing R]
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hm : IsMinimalComplex F) (n : ℕ) :
    ∀ i : ℤ,((frobeniusComplex R p n F).d i (i+1)).hom.range ≤
      (IsLocalRing.maximalIdeal R)^(p^n) •
        (⊤ : Submodule R ((frobeniusComplex R p n F).X (i+1))) := by
  intro i
  apply extendScalars_range_le (iterateFrobenius R p n) (F.d i (i+1)) _ _ (hm i)
  apply Ideal.map_le_iff_le_comap.mpr
  intro r hr
  change r^(p^n) ∈ (IsLocalRing.maximalIdeal R)^(p^n)
  exact Ideal.pow_mem_pow hr _

lemma acyclic_of_unit_nullhomotopy (F : CochainComplex (ModuleCat.{u} S) ℤ)
    (x : S) (hx : IsUnit x) (H : Homotopy (x • 𝟙 F) 0) : F.Acyclic := by
  obtain ⟨u,rfl⟩ := hx
  apply acyclic_of_contractible F
  simpa only [smul_smul,Units.inv_mul,one_smul,smul_zero] using H.smul (↑(u⁻¹):S)

lemma short_extension_acyclicAway [IsLocalRing R] [IsNoetherianRing R]
    (φ : R →+* S) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    (((baseChangeFunctor S (Localization.Away (φ x))).mapHomologicalComplex _).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj F)).Acyclic := by
  let G := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj F
  let A := Localization.Away (φ x)
  let f := algebraMap S A
  obtain ⟨a,ha⟩ := shortComplex_nullScalar_radical F hF hx
  have H := baseChange_nullhomotopy (S:=A) G (φ (x^a))
    (extendScalars_nullhomotopy φ F (x^a) ha.some)
  apply acyclic_of_unit_nullhomotopy _ (f (φ (x^a))) _ H
  rw [map_pow,map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (φ x)).pow a
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_DuttaMinimalEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]
  [Infinite (ResidueField D)]

 

theorem dutta_minimal_estimate_oai (hd : 0 < dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F)
    (hm : IsMinimalComplex F) :
    ∃ (A : ℝ) (c : ℕ),0≤A ∧ ∀ n : ℕ,c < p^n →
      multiplicity D*((p^n-c:ℕ):ℝ)^dimension D*
        ((Module.finrank D (F.X 0):ℝ)-A/((p^n-c:ℕ):ℝ)*
          ∑ i∈Finset.range (dimension D+1),(Module.finrank D (F.X (-(i:ℤ))):ℝ)) ≤
            ((p:ℝ)^n)^dimension D*duttaMultiplicity D p F := by
  classical
  obtain ⟨z,hz,hprim,he,c,hred⟩ := MinimalReduction.exists_minimal_reduction (R:=D)
  obtain ⟨ell,hlim,_,hparam,hK,hpos⟩ := exists_length_with_module_limit D p hd
  obtain ⟨A,hA,H⟩ := complex_estimate_allModule (dimension D) hd
  refine ⟨A,c,hA,?_⟩
  let C := PerfectClosure D p
  let φ := PerfectClosure.of D p
  let Z : Fin (dimension D) → C := fun i => φ (z i)
  let J₀ := Ideal.span (Set.range z)
  let J := Ideal.span (Set.range Z)
  have hmap (a : ℕ) : (parameterIdeal D z a).map φ =
      Ideal.span (Set.range (fun i => Z i^a)) := by
    simp only [parameterIdeal,Ideal.map_span,← Set.range_comp,Function.comp_def,map_pow,Z]
    rfl
  have hJ : J₀.map φ = J := by simpa only [parameterIdeal,pow_one] using hmap 1
  have hepos : 0 ≤ multiplicity D := le_of_lt (he ▸ hpos z hprim)
  have hmu : ell.value (ModuleCat.of C (C ⧸ J)) = ENNReal.ofReal (multiplicity D) := by
    have H := hparam z hprim 1 (by omega)
    have heq : parameterIdeal D z 1 = J₀ := by
      exact congrArg Ideal.span (congrArg Set.range (funext fun i => _root_.pow_one (z i)))
    rw [heq] at H
    change ell.value (ModuleCat.of C (C ⧸ J₀.map φ)) = _ at H
    rw [hJ,he] at H
    simpa only [Nat.cast_one,one_pow,one_mul] using H
  have hpowers (a : ℕ) (ha : 0<a) :
      ell.value (ModuleCat.of C (C ⧸ Ideal.span (Set.range (fun i => Z i^a)))) =
        (a:ℝ≥0∞)^dimension D*ENNReal.ofReal (multiplicity D) := by
    rw [← hmap a]
    rw [hparam z hprim a ha,he]
  have hkoszul (a : ℕ) (ha : 1≤a) (i : ℤ) (hi : i < 0) :
      ell.value ((Koszul.unit (List.ofFn (fun j => Z j^a))).homology i)=0 := by
    have hr : (Koszul.entryIdeal (List.ofFn (fun j => z j^a))).radical = maximalIdeal D := by
      rw [entryIdeal_ofFn]
      exact (Normalization.radical_span_powers z a (by omega)).trans hprim
    have hh := hK (List.ofFn (fun j => z j^a)) (by simp) hr i hi
    simpa only [List.map_ofFn,Function.comp_def,map_pow,Z] using hh
  intro n hn
  let s := p^n-c
  have hs : 0 < s := by dsimp [s]; omega
  let K := frobeniusComplex D p n F
  have hKfin : IsFiniteHomologyComplex D K := frobenius_finiteHomology p F hF n
  let G := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K
  have hfree (i) : Module.Free C (G.X i) := by
    let := hKfin.term_free i
    exact free_extendScalars φ (K.X i)
  have hfinite (i) : Module.Finite C (G.X i) := by
    let := hKfin.term_finite i
    exact finite_extendScalars φ (K.X i)
  have hrank (i : ℤ) : Module.finrank C (G.X i) = Module.finrank D (F.X i) := by
    let := hKfin.term_free i
    let := hKfin.term_finite i
    change Module.finrank C ((ModuleCat.extendScalars φ).obj (K.X i)) = _
    rw [finrank_extendScalars φ (K.X i)]
    let := hF.term_free i
    let := hF.term_finite i
    exact finrank_extendScalars (iterateFrobenius D p n) (F.X i)
  have hb (i : ℤ) (hi : i < -(dimension D:ℤ) ∨ 0 < i) : IsZero (G.X i) :=
    (ModuleCat.extendScalars φ).map_isZero (hKfin.bounded i hi)
  have hac (j) : (((baseChangeFunctor C (Localization.Away (Z j))).mapHomologicalComplex _).obj G).Acyclic :=
    short_extension_acyclicAway φ K hKfin (z j) (hz j)
  have hδ (i : ℤ) : (G.d i (i+1)).hom.range ≤ J^s • (⊤ : Submodule C (G.X (i+1))) := by
    apply extendScalars_range_le φ (K.d i (i+1)) ((maximalIdeal D)^(p^n)) (J^s)
      (frobenius_minimal_depth p F hm n i)
    have hbound : (maximalIdeal D)^(p^n) ≤ J₀ ^ s := by
      have H := hred s
      have hsc : s+c=p^n := by dsimp [s]; omega
      rwa [hsc] at H
    calc
      ((maximalIdeal D)^(p^n)).map φ ≤ (J₀ ^ s).map φ := Ideal.map_mono hbound
      _ = J^s := by rw [Ideal.map_pow,hJ]
  have halt : ∑ i∈Finset.range (dimension D+1),(-1:ℝ)^i*(Module.finrank C (G.X (-(i:ℤ))):ℝ)=0 := by
    simp_rw [hrank]
    exact short_rank_euler_zero hd F hF
  have hh := H Z ell (multiplicity D) hepos hmu hpowers hkoszul G hfree hfinite hb hac s hs hδ halt
  simp_rw [hrank] at hh
  rw [perfection_complex_value D p ell hlim hparam F hF n] at hh
  exact hh
end Lech.CharP

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.CharP.dutta_minimal_estimate_oai.{u} := @OAI.Lech.CharP.dutta_minimal_estimate_oai.{u}
