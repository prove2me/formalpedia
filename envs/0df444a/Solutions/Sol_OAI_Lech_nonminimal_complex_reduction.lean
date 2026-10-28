-- Prove2me | solution 1 for OAI.Lech.nonminimal_complex_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:09:12.797131+00:00
-- url     : https://prove2.me/submissions/2af8d9a9-3254-4e1d-9e30-a639f7dcc0bc

import Mathlib
import Definitions.Def_DuttaDomain
import Definitions.Def_OAIQ032L005
import Definitions.Def_OAIQ032L009
import Theorems.Thm_OAI_Lech_null_projector_contractible_splitting

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ElementaryContractibleProjector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex HomComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
variable (t : F.X (i+1) ⟶ F.X i)

lemma elementaryProjector_f_left :
    (elementaryProjector F i t).f i = F.d i (i+1) ≫ t := by
  rw [elementaryProjector,Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (i-1) i by simp)
    (show (ComplexShape.up ℤ).Rel i (i+1) by simp)]
  simp only [elementaryBackward,Cochain.single_v]
  rw [Cochain.single_v_eq_zero _ _ _ _ _ (by omega),zero_comp,add_zero]

lemma elementaryProjector_f_right :
    (elementaryProjector F i t).f (i+1) = t ≫ F.d i (i+1) := by
  rw [elementaryProjector,Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel i (i+1) by simp)
    (show (ComplexShape.up ℤ).Rel (i+1) (i+1+1) by simp)]
  simp only [elementaryBackward,Cochain.single_v]
  rw [Cochain.single_v_eq_zero _ _ _ _ _ (by omega),comp_zero,zero_add]

lemma elementaryProjector_f_other (j : ℤ) (hj : j ≠ i) (hj' : j ≠ i+1) :
    (elementaryProjector F i t).f j = 0 := by
  rw [elementaryProjector,Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℤ).Rel (j-1) j by simp)
    (show (ComplexShape.up ℤ).Rel j (j+1) by simp)]
  simp only [elementaryBackward]
  rw [Cochain.single_v_eq_zero _ _ _ _ _ (by omega),
    Cochain.single_v_eq_zero _ _ _ _ _ hj',comp_zero,zero_comp,add_zero]

lemma elementaryProjector_idempotent (ht : t ≫ F.d i (i+1) ≫ t = t) :
    elementaryProjector F i t ≫ elementaryProjector F i t = elementaryProjector F i t := by
  apply HomologicalComplex.hom_ext
  intro j
  simp only [comp_f]
  by_cases hj : j=i
  · subst j
    rw [elementaryProjector_f_left,Category.assoc,ht]
  · by_cases hj' : j=i+1
    · subst j
      rw [elementaryProjector_f_right,← Category.assoc,Category.assoc t,ht]
    · rw [elementaryProjector_f_other F i t j hj hj',zero_comp]
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FiniteFreeRetract
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]

lemma finite_free_retract {M N : ModuleCat.{u} R} [Module.Free R M] [Module.Finite R M]
    (i : N ⟶ M) (r : M ⟶ N) (hir : i ≫ r = 𝟙 N) :
    Module.Free R N ∧ Module.Finite R N := by
  have hr : Function.Surjective r := by
    intro x
    exact ⟨i x,congrArg (fun f : N ⟶ N => f x) hir⟩
  let : Module.Finite R N := Module.Finite.of_surjective r.hom hr
  let : Module.Flat R N := Module.Flat.of_retract i.hom r.hom
    (show r.hom.comp i.hom = LinearMap.id from congrArg ModuleCat.Hom.hom hir)
  exact ⟨Module.free_of_flat_of_isLocalRing,inferInstance⟩

omit [IsLocalRing R] in
lemma isZero_of_retract {M N : ModuleCat.{u} R}
    (i : N ⟶ M) (r : M ⟶ N) (hir : i ≫ r = 𝟙 N) (hM : IsZero M) : IsZero N := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← hir,hM.eq_of_tgt i 0,zero_comp]

end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NonminimalPivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M N : ModuleCat.{u} R} [Module.Free R N] [Module.Finite R N]

lemma exists_unit_pivot (f : M ⟶ N)
    (hf : ¬ f.hom.range ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :
    ∃ (x : M) (l : N →ₗ[R] R), l (f x) = 1 := by
  classical
  obtain ⟨y,hy,hy'⟩ := SetLike.not_le_iff_exists.mp hf
  obtain ⟨x,rfl⟩ := hy
  let b := Module.finBasis R N
  have hc : ∃ j, b.repr (f x) j ∉ IsLocalRing.maximalIdeal R := by
    by_contra! h
    apply hy'
    rw [← b.sum_repr (f x)]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem_smul (h j) Submodule.mem_top
  obtain ⟨j,hj⟩ := hc
  obtain ⟨u,hu⟩ := IsLocalRing.notMem_maximalIdeal.mp hj
  refine ⟨x,(↑(u⁻¹):R) • b.coord j,?_⟩
  change (↑(u⁻¹):R) * b.repr (f x) j = 1
  rw [← hu]
  exact Units.inv_mul u

lemma exists_nonzero_reverse_projector (f : M ⟶ N)
    (hf : ¬ f.hom.range ≤ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N)) :
    ∃ t : N ⟶ M, t ≫ f ≫ t = t ∧ f ≫ t ≠ 0 := by
  obtain ⟨x,l,hl⟩ := exists_unit_pivot f hf
  let t : N ⟶ M := ModuleCat.ofHom (l.smulRight x)
  have hx : x ≠ 0 := by
    intro hx
    rw [hx,map_zero,map_zero] at hl
    exact zero_ne_one hl
  refine ⟨t,?_,?_⟩
  · ext y
    change l (f (l y • x)) • x = l y • x
    rw [map_smul,map_smul,hl,smul_eq_mul,mul_one]
  · intro ht
    have hh := congrArg (fun g : M ⟶ M => g x) ht
    change l (f x) • x = 0 at hh
    rw [hl,one_smul] at hh
    exact hx hh
end Lech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_MinimalComplexReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
lemma nonminimal_complex_reduction_oai (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (hn : ¬ IsMinimalComplex F) :
    ∃ G : CochainComplex (ModuleCat.{u} R) ℤ,
      IsFiniteHomologyComplex R G ∧ Nonempty (HomotopyEquiv F G) ∧
        complexRankSum G < complexRankSum F := by
  classical
  obtain ⟨j,hj⟩ := not_forall.mp hn
  let := hF.term_free (j+1)
  let := hF.term_finite (j+1)
  obtain ⟨t,ht,htne⟩ := exists_nonzero_reverse_projector (F.d j (j+1)) hj
  let q := elementaryProjector F j t
  have hq : q ≫ q = q := elementaryProjector_idempotent F j t ht
  have hqn : q.f j ≠ 0 := by simpa only [q,elementaryProjector_f_left] using htne
  obtain ⟨G,K,i,r,a,b,hir,hab,hba,hs,hib,har,⟨e⟩⟩ :=
    null_projector_contractible_splitting F q hq (elementaryProjectorNull F j t)
  have hg (s : ℤ) : Module.Free R (G.X s) ∧ Module.Finite R (G.X s) := by
    let := hF.term_free s
    let := hF.term_finite s
    exact finite_free_retract (i.f s) (r.f s) (congrArg (fun u => u.f s) hir)
  have hk (s : ℤ) : Module.Free R (K.X s) ∧ Module.Finite R (K.X s) := by
    let := hF.term_free s
    let := hF.term_finite s
    exact finite_free_retract (a.f s) (b.f s) (congrArg (fun u => u.f s) hab)
  have hrank (s : ℤ) : Module.finrank R (F.X s) =
      Module.finrank R (G.X s) + Module.finrank R (K.X s) := by
    let := (hg s).1
    let := (hg s).2
    let := (hk s).1
    let := (hk s).2
    let ee := complementaryRetractEquiv (i.f s) (r.f s) (a.f s) (b.f s)
      (congrArg (fun u => u.f s) hir) (congrArg (fun u => u.f s) hab)
      (congrArg (fun u => u.f s) hs) (congrArg (fun u => u.f s) hib)
      (congrArg (fun u => u.f s) har)
    rw [ee.finrank_eq,Module.finrank_prod]
  have hG : IsFiniteHomologyComplex R G :=
    { term_free := fun s => (hg s).1
      term_finite := fun s => (hg s).2
      bounded := fun s hs => isZero_of_retract (i.f s) (r.f s)
        (congrArg (fun u => u.f s) hir) (hF.bounded s hs)
      homology_finite_length := fun s => by
        apply Module.length_ne_top_iff.mp
        rw [← (e.toHomologyIso s).toLinearEquiv.length_eq]
        exact Module.length_ne_top_iff.mpr (hF.homology_finite_length s) }
  have hKne : ¬ IsZero (K.X j) := by
    intro hz
    apply hqn
    rw [← hba]
    change b.f j ≫ a.f j = 0
    rw [hz.eq_of_tgt (b.f j) 0,zero_comp]
  have hpos : 0 < Module.finrank R (K.X j) := by
    let := (hk j).1
    let := (hk j).2
    apply (Module.finrank_pos_iff_of_free R (K.X j)).mpr
    exact not_subsingleton_iff_nontrivial.mp
      (fun hh => hKne (ModuleCat.isZero_iff_subsingleton.mpr hh))
  have hjbounds : -(dimension R:ℤ) ≤ j ∧ j ≤ 0 := by
    constructor
    · by_contra! h
      exact hqn ((hF.bounded j (Or.inl h)).eq_of_src _ _)
    · by_contra! h
      exact hqn ((hF.bounded j (Or.inr h)).eq_of_src _ _)
  have hjnat : -(((-j).toNat:ℕ):ℤ) = j := by omega
  refine ⟨G,hG,⟨e⟩,?_⟩
  apply Finset.sum_lt_sum
  · intro s _
    rw [hrank]
    omega
  · refine ⟨(-j).toNat,Finset.mem_range.mpr (by omega),?_⟩
    change Module.finrank R (G.X (-(((-j).toNat:ℕ):ℤ))) <
      Module.finrank R (F.X (-(((-j).toNat:ℕ):ℤ)))
    rw [hjnat,hrank]
    omega
end Lech

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.nonminimal_complex_reduction_oai.{u} := @OAI.Lech.nonminimal_complex_reduction_oai.{u}
