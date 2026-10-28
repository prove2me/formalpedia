-- Prove2me | solution 1 for OAI.Lech.Koszul.length_quotient_tensor_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:01:34.946637+00:00
-- url     : https://prove2.me/submissions/f3ffef13-5d4c-4eed-a9a0-81c00bf91795

import Mathlib
import Definitions.Def_OAIQ032L014
import Definitions.Def_OAIQ032L018

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

end Lech.Koszul

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_HomologyLengthDevissage
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.FiniteComplex
universe u
variable {R : Type u} [CommRing R]

lemma homology_length_iso (F G : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : F ≅ G) (i : ℤ) : Module.length R (F.homology i) = Module.length R (G.homology i) :=
  ((homologyFunctor _ _ i).mapIso e).toLinearEquiv.length_eq

 

theorem homology_length_le_sum
    (T : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    [T.Additive]
    (hT : ∀ (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)),
      (∀ j, (S.map (eval (ModuleCat R) (.up ℤ) j)).Splitting) →
      ∀ j, ((S.map T).map (eval (ModuleCat R) (.up ℤ) j)).Splitting)
    (m : ℤ) (N : ℕ) (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j)) :
    Module.length R ((T.obj F).homology i) ≤
      ∑ k∈Finset.range N, Module.length R
        ((T.obj ((single (ModuleCat R) (.up ℤ) (m+k)).obj (F.X (m+k)))).homology i) := by
  induction N generalizing F with
  | zero =>
    have hz := (homologyFunctor (ModuleCat R) (.up ℤ) i).map_isZero
      (T.map_isZero (isZero_of_X F (fun j => hb j (by omega))))
    have : Subsingleton ((T.obj F).homology i) := ModuleCat.isZero_iff_subsingleton.mp hz
    simp only [Finset.range_zero,Finset.sum_empty,le_zero_iff,Module.length_eq_zero]
  | succ N ih =>
    let n : ℤ := m+N
    have hn : ∀ j, n < j → IsZero (F.X j) := fun j hj => hb j (by
      right
      dsimp [n] at hj
      omega)
    let D := dropTop F n hn
    have hbD : ∀ j, j < m ∨ m + N ≤ j → IsZero (D.X j) := by
      intro j hj
      by_cases hjn : j=n
      · subst j
        exact dropTop_X_top F n hn
      · exact (hb j (by dsimp [n] at hjn; omega)).of_iso
          (dropTopXIso F n hn j hjn).symm
    have hD := ih D hbD
    have he (k : ℕ) (hk : k∈Finset.range N) :
        Module.length R ((T.obj ((single (ModuleCat R) (.up ℤ) (m+k)).obj (D.X (m+k)))).homology i) =
        Module.length R ((T.obj ((single (ModuleCat R) (.up ℤ) (m+k)).obj (F.X (m+k)))).homology i) :=
      (homology_length_iso _ _
        (T.mapIso ((single (ModuleCat R) (.up ℤ) (m+k)).mapIso
          (dropTopXIso F n hn (m+k) (by dsimp [n]; simp only [Finset.mem_range] at hk; omega)))) i).symm
    have hs : ((topShortComplex F n hn).map T).ShortExact :=
      shortExact_of_degreewise_shortExact _ (fun j =>
        (hT _ (topSplitting F n hn) j).shortExact)
    have hl := Koszul.length_le_sum_of_exact _ (hs.homology_exact₂ i)
    change Module.length R ((T.obj F).homology i) ≤
      Module.length R ((T.obj ((single (ModuleCat R) (.up ℤ) n).obj (F.X n))).homology i)+
      Module.length R ((T.obj D).homology i) at hl
    rw [Finset.sum_congr rfl he] at hD
    simpa only [Finset.sum_range_succ,add_comm,n] using
      hl.trans (add_le_add le_rfl hD)
end Lech.FiniteComplex

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_AdditiveLength
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma additive_length_pi (T : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [T.Additive]
    {ι : Type} [Fintype ι] (M : ι → ModuleCat.{u} R) :
    Module.length R (T.obj (ModuleCat.of R (∀ i,M i))) =
      ∑ i,Module.length R (T.obj (M i)) := by
  let e := T.mapIso (ModuleCat.biproductIsoPi M).symm ≪≫
    T.mapBiproduct M ≪≫ ModuleCat.biproductIsoPi (fun i : ι => T.obj (M i))
  exact e.toLinearEquiv.length_eq.trans (Module.length_pi_of_fintype _ _)

lemma additive_length_finite_free [Nontrivial R] (T : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [T.Additive]
    (M : ModuleCat.{u} R) [Module.Free R M] [Module.Finite R M] :
    Module.length R (T.obj M) = Module.finrank R M •
      Module.length R (T.obj (ModuleCat.of R R)) := by
  classical
  let b := Module.Free.chooseBasis R M
  let := Module.Free.ChooseBasisIndex.fintype R M
  let e := (b.reindex (Fintype.equivFin _)).equivFun.toModuleIso
  rw [(T.mapIso e).toLinearEquiv.length_eq]
  rw [additive_length_pi T (fun _ : Fin (Fintype.card (Module.Free.ChooseBasisIndex R M)) => ModuleCat.of R R)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  exact (Module.finrank_eq_card_basis b).symm
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_KoszulFiniteComplexBound
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.instAdditiveCochainComplexIntTensorFunctor_1 _root_.OAI.Lech.Koszul.moduleQuotient_linear _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.Koszul.tensorFunctor_linear _root_.OAI.Lech.extendScalars_additive
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

lemma length_quotient_tensor_le_sum_oai (I : Ideal R) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j))
    (hfree : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j)) :
    Module.length R ((tensor zs ((complexQuotient I (.up ℤ)).obj F)).homology i) ≤
      ∑ k∈Finset.range N, Module.finrank R (F.X (m+k)) • Module.length R
        ((tensor zs ((complexQuotient I (.up ℤ)).obj
          ((single (ModuleCat R) (.up ℤ) (m+k)).obj (ModuleCat.of R R)))).homology i) := by
  let T : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _ := complexQuotient I (.up ℤ) ⋙ tensorFunctor zs
  have hT (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
      (σ : ∀ j,(S.map (eval _ (.up ℤ) j)).Splitting) (i : ℤ) :
      ((S.map T).map (eval _ (.up ℤ) i)).Splitting :=
    tensorSplitting zs (S.map (complexQuotient I (.up ℤ)))
      (fun j => (σ j).map (moduleQuotient I)) i
  have hl := FiniteComplex.homology_length_le_sum T hT m N F i hb
  refine hl.trans_eq ?_
  apply Finset.sum_congr rfl
  intro k hk
  have := hfree (m+k)
  have := hfin (m+k)
  exact additive_length_finite_free
    (single (ModuleCat R) (.up ℤ) (m+k) ⋙ T ⋙ homologyFunctor _ (.up ℤ) i) (F.X (m+k))



end Lech.Koszul

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.Koszul.length_quotient_tensor_le_sum_oai.{u} := @OAI.Lech.Koszul.length_quotient_tensor_le_sum_oai.{u}
