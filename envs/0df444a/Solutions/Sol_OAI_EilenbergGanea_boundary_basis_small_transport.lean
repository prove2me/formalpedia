-- Prove2me | solution 1 for OAI.EilenbergGanea.boundary_basis_small_transport
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T03:27:57.197342+00:00
-- url     : https://prove2.me/submissions/d63c8f76-0c1a-4c2f-8504-d1d989056bcd

import Mathlib
import Definitions.Def_OAIEGC003
import Theorems.Thm_OAI_EilenbergGanea_aligned_presentation_small_transport

section
-- module Solutions.OAIEG.SmallHolonomy
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea

variable {Γ S H : Type*} [Group Γ] [Group H]

 theorem pathProduct_conjugate_loop (v : S → Γ) (a : Γ → S → H)
    (u r : FreeGroup S) (hr : wordValue v r = 1) (g : Γ) :
    pathProduct v a (u*r*u⁻¹) g = pathProduct v a u g *
      pathProduct v a r (g * wordValue v u) * (pathProduct v a u g)⁻¹ := by
  rw [pathProduct_mul, pathProduct_mul, pathProduct_inv, map_mul, hr, mul_one]
  simp only [mul_inv_cancel_right]

 theorem pathChain_conjugate (v : S → Γ) (u r : FreeGroup S)
    (hr : wordValue v r = 1) (g : Γ) :
    pathChain v (u*r*u⁻¹) g = pathChain v r (g * wordValue v u) := by
  simp only [pathChain, pathProduct_conjugate_loop v _ u r hr g,
    toAdd_mul, toAdd_inv]
  abel

end EilenbergGanea

open scoped Quaternion


end

end OAI
end

section
-- module Solutions.OAIEG.PresentationComparison
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
section ChainProjection
variable {Γ D S T R : Type*} [Group Γ] [Group D]

theorem pathChain_translate (v : S → Γ) (w : FreeGroup S) (g h : Γ) :
    translateChains g (pathChain v w h) = pathChain v w (g*h) := by
  induction w using OAI.freeGroupInductionOn generalizing h with
  | one => simp
  | of s => simp
  | inv_of s ih => simp only [pathChain_inv, map_neg, ih, mul_assoc]
  | mul w z hw hz => simp only [pathChain_mul, map_add, hw, hz, mul_assoc]

end ChainProjection
end EilenbergGanea

end

end OAI
end

section
-- module Solutions.OAIEG.PresentationAlignment
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

/-! Actual word and cycle-basis alignment. -/
namespace EilenbergGanea
section WordRealization
variable {Γ S R : Type*} [Group Γ]

theorem pathChain_zpow_loop (v : S → Γ) (w : FreeGroup S)
    (hw : wordValue v w = 1) (n : ℤ) (g : Γ) :
    pathChain v (w ^ n) g = n • pathChain v w g := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      rw [zpow_add, zpow_one, pathChain_mul, map_zpow, hw, one_zpow, mul_one, ih]
      simp [add_zsmul]
  | pred n ih =>
      rw [zpow_sub, zpow_one, pathChain_mul, map_zpow, hw, one_zpow, mul_one,
        pathChain_inv, hw, inv_one, mul_one, ih]
      simp only [sub_eq_add_neg, add_zsmul, neg_zsmul, one_zsmul]

/-- Every finitely supported integral relator combination is realized by a
finite word in the same normal closure. Surjectivity supplies the finitely
many conjugating words; no infinite product of presentation moves occurs. -/
theorem realize_relator_chain (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1)
    (c : (Γ × R) →₀ ℤ) :
    ∃ w ∈ Subgroup.normalClosure (Set.range r),
      pathChain v w 1 = relatorChainMap v r c := by
  classical
  induction c using Finsupp.induction with
  | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | @single_add a n c ha hn ih =>
      obtain ⟨w,hw,hcw⟩ := ih
      obtain ⟨u,hu⟩ := hv a.1
      let z := u * r a.2 * u⁻¹
      have hz : z ∈ Subgroup.normalClosure (Set.range r) :=
        (Subgroup.normalClosure_normal (s := Set.range r)).conj_mem _
          (Subgroup.subset_normalClosure (Set.mem_range_self a.2)) u
      have hzw : wordValue v z = 1 := by simp [z,hr]
      refine ⟨z ^ n * w, Subgroup.mul_mem _ (Subgroup.zpow_mem _ hz n) hw, ?_⟩
      rw [pathChain_mul, map_zpow, hzw, one_zpow, mul_one, pathChain_zpow_loop _ _ hzw,
        hcw, map_add]
      congr 1
      rw [pathChain_conjugate v u _ (hr a.2), one_mul, hu]
      simp [relatorChainMap]

end WordRealization
end EilenbergGanea
namespace EilenbergGanea
section RelatorShears
variable {Γ S R I : Type*} [Group Γ]

theorem relatorChainMap_equivariant (v : S → Γ) (r : R → FreeGroup S) :
    ChainsEquivariant (relatorChainMap v r) := by
  intro g c
  have he : (relatorChainMap v r).comp (translateChains g) =
      (translateChains g).comp (relatorChainMap v r) := by
    apply Finsupp.lhom_ext
    rintro ⟨h,i⟩ n
    simp only [LinearMap.comp_apply, translateChains_single, relatorChainMap,
      Finsupp.linearCombination_single, map_smul, pathChain_translate]
  exact LinearMap.congr_fun he c

theorem normal_relators_trivial (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) :
    Subgroup.normalClosure (Set.range r) ≤ (wordValue v).ker := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i,rfl⟩
  exact hr i

/-- A whole column-finite shear is realized by honest finite relator words,
including when the relator alphabets have arbitrary cardinality. -/
theorem shear_relators (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (r : R → FreeGroup S) (u : I → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (hu : ∀ i, wordValue v (u i) = 1)
    (C : BasedChains Γ I →ₗ[ℤ] BasedChains Γ R) (hC : ChainsEquivariant C) :
    ∃ u' : I → FreeGroup S,
      (∀ i, wordValue v (u' i) = 1) ∧
      Subgroup.normalClosure (Set.range r ∪ Set.range u') =
        Subgroup.normalClosure (Set.range r ∪ Set.range u) ∧
      relatorChainMap v u' = relatorChainMap v u + (relatorChainMap v r).comp C := by
  classical
  choose p hp hc using fun i => realize_relator_chain v hv r hr (C (Finsupp.single (1,i) 1))
  let u' : I → FreeGroup S := fun i => u i * p i
  have hpr (i) : wordValue v (p i) = 1 := normal_relators_trivial v r hr (hp i)
  have hu' (i) : wordValue v (u' i) = 1 := by simp [u',hu,hpr]
  refine ⟨u',hu',?_,?_⟩
  · apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      rintro _ (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact Subgroup.subset_normalClosure (Or.inl (Set.mem_range_self i))
      · exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure (Or.inr (Set.mem_range_self i)))
          (Subgroup.normalClosure_mono Set.subset_union_left (hp i))
    · apply Subgroup.normalClosure_le_normal
      rintro _ (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact Subgroup.subset_normalClosure (Or.inl (Set.mem_range_self i))
      · have h : u' i * (p i)⁻¹ ∈ Subgroup.normalClosure (Set.range r ∪ Set.range u') :=
          Subgroup.mul_mem _ (Subgroup.subset_normalClosure (Or.inr (Set.mem_range_self i)))
            (Subgroup.inv_mem _ (Subgroup.normalClosure_mono Set.subset_union_left (hp i)))
        simpa [u'] using h
  · have hb (i) : pathChain v (u' i) 1 = pathChain v (u i) 1 +
        relatorChainMap v r (C (Finsupp.single (1,i) 1)) := by
      simp only [u',pathChain_mul,hu,mul_one,hc]
    have hbg (g : Γ) (i : I) : pathChain v (u' i) g = pathChain v (u i) g +
        relatorChainMap v r (C (Finsupp.single (g,i) 1)) := by
      have h := congrArg (translateChains g) (hb i)
      rw [map_add,pathChain_translate,pathChain_translate,mul_one,
        ← relatorChainMap_equivariant v r g, ← hC g, translateChains_single,mul_one] at h
      exact h
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    have hn : Finsupp.single (g,i) n = n • Finsupp.single (g,i) (1 : ℤ) := by simp
    simpa only [hn, map_smul, LinearMap.add_apply, LinearMap.comp_apply,
      relatorChainMap_single, one_smul, smul_add] using congrArg (n • ·) (hbg g i)

/-- The source's three shears P,Q,P, at the level of relator words rather
than merely chain matrices. No infinite product or cardinality restriction. -/
theorem block_word_alignment (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (r : R → FreeGroup S) (u : I → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (hu : ∀ i, wordValue v (u i) = 1)
    (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ I)
    (hA : ChainsEquivariant A.toLinearMap) :
    ∃ (r' : R → FreeGroup S) (u' : I → FreeGroup S),
      (∀ i, wordValue v (r' i) = 1) ∧ (∀ i, wordValue v (u' i) = 1) ∧
      Subgroup.normalClosure (Set.range r' ∪ Set.range u') =
        Subgroup.normalClosure (Set.range r ∪ Set.range u) ∧
      relatorChainMap v r' = -((relatorChainMap v u).comp A.toLinearMap) ∧
      relatorChainMap v u' = (relatorChainMap v r).comp A.symm.toLinearMap := by
  have hAi := ChainsEquivariant.symm A hA
  have hnA : ChainsEquivariant (-A.toLinearMap) := by
    intro g c
    simp only [LinearMap.neg_apply, map_neg]
    exact congrArg Neg.neg (hA g c)
  obtain ⟨u₁,hu₁,hN₁,hD₁⟩ := shear_relators v hv r u hr hu A.symm.toLinearMap hAi
  obtain ⟨r₂,hr₂,hN₂,hD₂⟩ := shear_relators v hv u₁ r hu₁ hr (-A.toLinearMap) hnA
  have hD₂' : relatorChainMap v r₂ = -((relatorChainMap v u).comp A.toLinearMap) := by
    rw [hD₂,hD₁]
    ext c
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply,
      map_neg, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    abel_nf
  obtain ⟨u₃,hu₃,hN₃,hD₃⟩ := shear_relators v hv r₂ u₁ hr₂ hu₁ A.symm.toLinearMap hAi
  refine ⟨r₂,u₃,hr₂,hu₃,?_,hD₂',?_⟩
  · rw [hN₃,Set.union_comm (Set.range r₂) (Set.range u₁),hN₂,
      Set.union_comm (Set.range u₁) (Set.range r),hN₁]
  · rw [hD₃,hD₁,hD₂']
    ext c
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    abel_nf

end RelatorShears
end EilenbergGanea

namespace EilenbergGanea
section TrivialPresentationExtension
variable {Γ S T R : Type*} [Group Γ]

theorem unitExtendedRelators_trivial (v : S → Γ) (r : R → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (i : R ⊕ T) :
    wordValue (Sum.elim v (fun _ : T => 1)) (unitExtendedRelators r i) = 1 := by
  rcases i with i | t
  · change wordValue _ (FreeGroup.map Sum.inl (r i)) = 1
    have he : (wordValue (Sum.elim v (fun _ : T => 1))).comp (FreeGroup.map Sum.inl) =
        wordValue v := by
      apply FreeGroup.ext_hom
      intro s
      simp [wordValue]
    exact (DFunLike.congr_fun he (r i)).trans (hr i)
  · simp [unitExtendedRelators,wordValue]

/-- Adjoining arbitrarily many generators of value one and their unit relators
preserves the actual presentation, not merely its abelianization. -/
theorem unitExtension_normalClosure (v : S → Γ) (r : R → FreeGroup S)
    (hp : (wordValue v).ker = Subgroup.normalClosure (Set.range r)) :
    (wordValue (Sum.elim v (fun _ : T => 1))).ker =
      Subgroup.normalClosure (Set.range (unitExtendedRelators r : R ⊕ T → _)) := by
  let N := Subgroup.normalClosure (Set.range (unitExtendedRelators r : R ⊕ T → _))
  have hr (i) : wordValue v (r i) = 1 := by
    change r i ∈ (wordValue v).ker
    rw [hp]
    exact Subgroup.subset_normalClosure (Set.mem_range_self i)
  apply le_antisymm
  · intro w hw
    have hcomp : (wordValue v).comp eraseExtra =
        wordValue (Sum.elim v (fun _ : T => 1)) := by
      apply FreeGroup.ext_hom
      intro s
      rcases s with s | t <;> simp [eraseExtra,wordValue]
    have hker : eraseExtra w ∈ Subgroup.normalClosure (Set.range r) := by
      rw [← hp]
      exact (DFunLike.congr_fun hcomp w).trans hw
    have hmap : FreeGroup.map Sum.inl (eraseExtra w) ∈ N := by
      apply Subgroup.normalClosure_mono (s := (FreeGroup.map Sum.inl) '' Set.range r)
        (by rintro _ ⟨a,⟨i,rfl⟩,rfl⟩; exact ⟨Sum.inl i,rfl⟩)
      exact Subgroup.comap_normalClosure_image_ge _ (FreeGroup.map Sum.inl) hker
    have heq : (QuotientGroup.mk' N : FreeGroup (S ⊕ T) →* _) =
        ((QuotientGroup.mk' N).comp (FreeGroup.map Sum.inl)).comp eraseExtra := by
      apply FreeGroup.ext_hom
      intro s
      rcases s with s | t
      · simp [eraseExtra]
      · simp only [MonoidHom.comp_apply,eraseExtra,FreeGroup.lift_apply_of,Sum.elim_inr,map_one]
        apply (QuotientGroup.eq_one_iff _).mpr
        exact Subgroup.subset_normalClosure ⟨Sum.inr t,rfl⟩
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' N) w = 1
    rw [DFunLike.congr_fun heq w]
    exact (QuotientGroup.eq_one_iff _).mpr hmap
  · exact normal_relators_trivial _ _ (unitExtendedRelators_trivial v r hr)

/-- The chain matrix of adjoining unit relators is a block diagonal matrix. -/
theorem unitExtension_chain (v : S → Γ) (r : R → FreeGroup S)
    (c : BasedChains Γ (R ⊕ T)) :
    sumChainsEquiv (relatorChainMap (Sum.elim v (fun _ : T => 1))
      (unitExtendedRelators r) c) =
      (relatorChainMap v r (sumChainsEquiv c).1,(sumChainsEquiv c).2) := by
  have hi (w : FreeGroup S) (g : Γ) :
      sumChainsEquiv (pathChain (Sum.elim v (fun _ : T => 1)) (FreeGroup.map Sum.inl w) g) =
        (pathChain v w g,0) := by
    induction w using OAI.freeGroupInductionOn generalizing g with
    | one => simp only [map_one,pathChain_one,map_zero]; rfl
    | of s => simp
    | inv_of s _ih => simp [pathChain_inv,wordValue]
    | mul w z hw hz =>
      have hv : wordValue (Sum.elim v (fun _ : T => 1)) (FreeGroup.map Sum.inl w) = wordValue v w := by
        have h : (wordValue (Sum.elim v (fun _ : T => 1))).comp (FreeGroup.map Sum.inl) = wordValue v := by
          apply FreeGroup.ext_hom
          intro s
          simp [wordValue]
        exact DFunLike.congr_fun h w
      simp only [map_mul,pathChain_mul,map_add,hw,hz,hv,Prod.mk_add_mk,add_zero]
  have he : sumChainsEquiv.toLinearMap.comp (relatorChainMap
      (Sum.elim v (fun _ : T => 1)) (unitExtendedRelators r)) =
      (((relatorChainMap v r).comp (LinearMap.fst ℤ _ _)).prod
        (LinearMap.snd ℤ _ _)).comp sumChainsEquiv.toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨g,i | t⟩ n
    · simp [unitExtendedRelators,hi]
    · simp [unitExtendedRelators]
  exact LinearMap.congr_fun he c

end TrivialPresentationExtension
end EilenbergGanea

namespace EilenbergGanea
section UnitExtensionBasis
variable {Γ S T R : Type*} [Group Γ]

theorem unitExtensionBasis_value (v : S → Γ) (r : R → FreeGroup S)
    (B : BasedChains Γ R ≃ₗ[ℤ] cycles v)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v r c)
    (c : BasedChains Γ (R ⊕ T)) :
    (unitExtensionBasis v B c : BasedChains Γ (S ⊕ T)) =
      relatorChainMap (Sum.elim v (fun _ : T => 1)) (unitExtendedRelators r) c := by
  apply sumChainsEquiv.injective
  rw [unitExtension_chain]
  change sumChainsEquiv (sumChainsEquiv.symm
    ((B (sumChainsEquiv c).1).val,(sumChainsEquiv c).2)) = _
  rw [LinearEquiv.apply_symm_apply,hB]

/-- Equivariance is automatic for an isomorphism whose columns are actual path
chains. This derives, rather than assumes, equivariance of its inverse. -/
theorem chainBasisCoordinate_equivariant (v : S → Γ)
    (r : R → FreeGroup S) (u : T → FreeGroup S)
    (E : BasedChains Γ R ≃ₗ[ℤ] cycles v)
    (B : BasedChains Γ T ≃ₗ[ℤ] cycles v)
    (hE : ∀ c, (E c : BasedChains Γ S) = relatorChainMap v r c)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v u c) :
    ChainsEquivariant (E.trans B.symm).toLinearMap := by
  intro g c
  apply B.injective
  apply Subtype.ext
  change (B (B.symm (E (translateChains g c)))).val =
    (B (translateChains g (B.symm (E c)))).val
  rw [B.apply_symm_apply,hE,hB,relatorChainMap_equivariant v u g]
  rw [← hB,B.apply_symm_apply,hE]
  exact relatorChainMap_equivariant v r g c

end UnitExtensionBasis
end EilenbergGanea

namespace EilenbergGanea
section Nielsen
variable {Γ S T A R : Type*} [Group Γ]

theorem nielsen_wordValue (v : S → Γ) (w : T → Γ) (a : T → FreeGroup S) :
    (wordValue (Sum.elim v w)).comp (nielsenEquiv a).toMonoidHom =
      wordValue (Sum.elim v (fun t => w t * wordValue v (a t))) := by
  have hi (u : FreeGroup S) : wordValue (Sum.elim v w) (FreeGroup.map Sum.inl u) =
      wordValue v u := by
    have h : (wordValue (Sum.elim v w)).comp (FreeGroup.map Sum.inl) = wordValue v := by
      apply FreeGroup.ext_hom
      intro s
      simp [wordValue]
    exact DFunLike.congr_fun h u
  apply FreeGroup.ext_hom
  intro s
  rcases s with s | t
  · simp [nielsenHom,wordValue]
  · change wordValue (Sum.elim v w) (nielsenHom a (FreeGroup.of (.inr t))) = _
    rw [nielsenHom_of_right,map_mul,hi]
    simp [wordValue]

theorem wordPresentation_transport (v : S → Γ) (w : T → Γ)
    (e : FreeGroup S ≃* FreeGroup T)
    (he : (wordValue w).comp e.toMonoidHom = wordValue v)
    (r : R → FreeGroup S)
    (hp : (wordValue v).ker = Subgroup.normalClosure (Set.range r)) :
    (wordValue w).ker = Subgroup.normalClosure (Set.range (fun i => e (r i))) := by
  have hi : (wordValue v).comp e.symm.toMonoidHom = wordValue w := by
    apply FreeGroup.ext_hom
    intro t
    simpa using (DFunLike.congr_fun he (e.symm (FreeGroup.of t))).symm
  change (wordValue w).ker = Subgroup.normalClosure (Set.range (e ∘ r))
  rw [Set.range_comp]
  change (wordValue w).ker = Subgroup.normalClosure (e.toMonoidHom '' Set.range r)
  rw [← Subgroup.map_normalClosure _ e.toMonoidHom e.surjective, ← hp]
  ext a
  constructor
  · intro ha
    refine ⟨e.symm a,?_,e.apply_symm_apply a⟩
    exact (DFunLike.congr_fun hi a).trans ha
  · rintro ⟨b,hb,rfl⟩
    exact (DFunLike.congr_fun he b).trans hb

theorem wordBasisTransport_value (v : S → Γ) (w : T → Γ)
    (e : FreeGroup S ≃* FreeGroup T)
    (he : (wordValue w).comp e.toMonoidHom = wordValue v)
    (B : BasedChains Γ R ≃ₗ[ℤ] cycles v) (r : R → FreeGroup S)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v r c)
    (c : BasedChains Γ R) :
    (wordBasisTransport v w e he B c : BasedChains Γ T) =
      relatorChainMap w (fun i => e (r i)) c := by
  change relatorChainMap w (fun s => e (FreeGroup.of s)) (B c).val = _
  rw [hB]
  have hh : (relatorChainMap w (fun s => e (FreeGroup.of s))).comp (relatorChainMap v r) =
      relatorChainMap w (fun i => e (r i)) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    simp only [LinearMap.comp_apply,relatorChainMap_single,map_zsmul]
    exact congrArg (n • ·) (pathChain_hom v w e.toMonoidHom he (r i) g)
  exact LinearMap.congr_fun hh c

end Nielsen
end EilenbergGanea

namespace EilenbergGanea
section GeneratorAlignment
variable {Γ S T A R : Type*} [Group Γ]

theorem wordValue_congr_alphabet (v : S → Γ) (w : T → Γ) (e : S ≃ T)
    (h : ∀ s, w (e s) = v s) :
    (wordValue w).comp (freeGroupCongr e).toMonoidHom = wordValue v := by
  apply FreeGroup.ext_hom
  intro s
  simpa [wordValue] using h s

theorem wordRelators_transport_trivial (v : S → Γ) (w : T → Γ)
    (e : FreeGroup S ≃* FreeGroup T)
    (he : (wordValue w).comp e.toMonoidHom = wordValue v)
    (r : R → FreeGroup S) (hr : ∀ i, wordValue v (r i) = 1) :
    ∀ i, wordValue w (e (r i)) = 1 := by
  intro i
  exact (DFunLike.congr_fun he (r i)).trans (hr i)

/-- Generator change starting with an actual boundary-basis presentation,
not with an assumed aligned one. -/
theorem align_generators (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (a : A → Γ) (ha : Function.Surjective (wordValue a))
    (r : R → FreeGroup A) (hr : ∀ i, wordValue a (r i) = 1)
    (hp : (wordValue a).ker = Subgroup.normalClosure (Set.range r))
    (B : BasedChains Γ R ≃ₗ[ℤ] cycles a)
    (hB : ∀ c, (B c : BasedChains Γ A) = relatorChainMap a r c) :
    ∃ (r' : R ⊕ S → FreeGroup (S ⊕ A))
      (B' : BasedChains Γ (R ⊕ S) ≃ₗ[ℤ] cycles (Sum.elim v (fun _ : A => 1))),
      (∀ i, wordValue (Sum.elim v (fun _ : A => 1)) (r' i) = 1) ∧
      (wordValue (Sum.elim v (fun _ : A => 1))).ker =
        Subgroup.normalClosure (Set.range r') ∧
      ∀ c, (B' c : BasedChains Γ (S ⊕ A)) =
        relatorChainMap (Sum.elim v (fun _ : A => 1)) r' c := by
  classical
  choose f hf using fun s => ha (v s)
  choose g hg using fun t => hv (a t)
  let v₀ : A ⊕ S → Γ := Sum.elim a (fun _ => 1)
  let v₁ : A ⊕ S → Γ := Sum.elim a v
  let v₂ : S ⊕ A → Γ := Sum.elim v a
  let v₃ : S ⊕ A → Γ := Sum.elim v (fun _ => 1)
  let e₁ := nielsenEquiv (fun s => (f s)⁻¹)
  let e₂ := freeGroupCongr (Equiv.sumComm A S)
  let e₃ := nielsenEquiv g
  have he₁ : (wordValue v₁).comp e₁.toMonoidHom = wordValue v₀ := by
    change (wordValue (Sum.elim a v)).comp
      (nielsenEquiv (fun s => (f s)⁻¹)).toMonoidHom = _
    simpa only [map_inv,hf,mul_inv_cancel] using
      nielsen_wordValue a v (fun s => (f s)⁻¹)
  have he₂ : (wordValue v₂).comp e₂.toMonoidHom = wordValue v₁ := by
    apply wordValue_congr_alphabet
    intro s
    rcases s with t | s <;> rfl
  have he₃ : (wordValue v₃).comp e₃.toMonoidHom = wordValue v₂ := by
    change (wordValue (Sum.elim v (fun _ : A => 1))).comp
      (nielsenEquiv g).toMonoidHom = _
    simpa only [one_mul,hg] using nielsen_wordValue v (fun _ : A => 1) g
  let r₀ : R ⊕ S → FreeGroup (A ⊕ S) := unitExtendedRelators r
  let r₁ : R ⊕ S → FreeGroup (A ⊕ S) := fun i => e₁ (r₀ i)
  let r₂ : R ⊕ S → FreeGroup (S ⊕ A) := fun i => e₂ (r₁ i)
  let r₃ : R ⊕ S → FreeGroup (S ⊕ A) := fun i => e₃ (r₂ i)
  let B₀ : BasedChains Γ (R ⊕ S) ≃ₗ[ℤ] cycles v₀ := unitExtensionBasis a B
  let B₁ := wordBasisTransport v₀ v₁ e₁ he₁ B₀
  let B₂ := wordBasisTransport v₁ v₂ e₂ he₂ B₁
  let B₃ := wordBasisTransport v₂ v₃ e₃ he₃ B₂
  have hr₀ : ∀ i, wordValue v₀ (r₀ i) = 1 := unitExtendedRelators_trivial a r hr
  have hr₁ := wordRelators_transport_trivial v₀ v₁ e₁ he₁ r₀ hr₀
  have hr₂ := wordRelators_transport_trivial v₁ v₂ e₂ he₂ r₁ hr₁
  have hr₃ := wordRelators_transport_trivial v₂ v₃ e₃ he₃ r₂ hr₂
  have hp₀ : (wordValue v₀).ker = Subgroup.normalClosure (Set.range r₀) :=
    unitExtension_normalClosure a r hp
  have hp₁ := wordPresentation_transport v₀ v₁ e₁ he₁ r₀ hp₀
  have hp₂ := wordPresentation_transport v₁ v₂ e₂ he₂ r₁ hp₁
  have hp₃ := wordPresentation_transport v₂ v₃ e₃ he₃ r₂ hp₂
  have hB₀ : ∀ c, (B₀ c : BasedChains Γ (A ⊕ S)) = relatorChainMap v₀ r₀ c :=
    unitExtensionBasis_value a r B hB
  have hB₁ := wordBasisTransport_value v₀ v₁ e₁ he₁ B₀ r₀ hB₀
  have hB₂ := wordBasisTransport_value v₁ v₂ e₂ he₂ B₁ r₁ hB₁
  have hB₃ := wordBasisTransport_value v₂ v₃ e₃ he₃ B₂ r₂ hB₂
  exact ⟨r₃,B₃,hr₃,hp₃,hB₃⟩

end GeneratorAlignment
end EilenbergGanea

namespace EilenbergGanea
section RelatorBlocks
variable {Γ S T R I : Type*} [Group Γ]

theorem relatorChainMap_sum (v : S → Γ) (r : R → FreeGroup S) (u : I → FreeGroup S)
    (c : BasedChains Γ (R ⊕ I)) :
    relatorChainMap v (Sum.elim r u) c =
      relatorChainMap v r (sumChainsEquiv c).1 + relatorChainMap v u (sumChainsEquiv c).2 := by
  have h : relatorChainMap v (Sum.elim r u) =
      ((relatorChainMap v r).comp (LinearMap.fst ℤ _ _) +
        (relatorChainMap v u).comp (LinearMap.snd ℤ _ _)).comp sumChainsEquiv.toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨g,i | j⟩ n <;> simp
  exact LinearMap.congr_fun h c

theorem sumChains_pathChain_left (v : S → Γ) (w : FreeGroup S) (g : Γ) :
    sumChainsEquiv (pathChain (Sum.elim v (fun _ : T => 1)) (FreeGroup.map Sum.inl w) g) =
      (pathChain v w g,0) := by
  induction w using OAI.freeGroupInductionOn generalizing g with
  | one => simp only [map_one,pathChain_one,map_zero]; rfl
  | of s => simp
  | inv_of s _ih => simp [pathChain_inv,wordValue]
  | mul w z hw hz =>
    have hv : wordValue (Sum.elim v (fun _ : T => 1)) (FreeGroup.map Sum.inl w) = wordValue v w := by
      have h : (wordValue (Sum.elim v (fun _ : T => 1))).comp (FreeGroup.map Sum.inl) = wordValue v := by
        apply FreeGroup.ext_hom
        intro s
        simp [wordValue]
      exact DFunLike.congr_fun h w
    simp only [map_mul,pathChain_mul,map_add,hw,hz,hv,Prod.mk_add_mk,add_zero]

theorem sumChains_relatorMap_left (v : S → Γ) (r : R → FreeGroup S) (c : BasedChains Γ R) :
    sumChainsEquiv (relatorChainMap (Sum.elim v (fun _ : T => 1))
      (fun i => FreeGroup.map Sum.inl (r i)) c) = (relatorChainMap v r c,0) := by
  have h : sumChainsEquiv.toLinearMap.comp (relatorChainMap
      (Sum.elim v (fun _ : T => 1)) (fun i => FreeGroup.map Sum.inl (r i))) =
      (relatorChainMap v r).prod 0 := by
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    simp [sumChains_pathChain_left]
  exact LinearMap.congr_fun h c

theorem sumChains_relatorMap_right (v : S → Γ) (c : BasedChains Γ T) :
    sumChainsEquiv (relatorChainMap (Sum.elim v (fun _ : T => 1))
      (fun i => FreeGroup.of (.inr i)) c) = (0,c) := by
  have h : sumChainsEquiv.toLinearMap.comp (relatorChainMap
      (Sum.elim v (fun _ : T => 1)) (fun i => FreeGroup.of (.inr i))) =
      (0 : BasedChains Γ T →ₗ[ℤ] BasedChains Γ S).prod LinearMap.id := by
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    simp
  exact LinearMap.congr_fun h c

theorem range_sumElim {α β γ : Type*} (f : α → γ) (g : β → γ) :
    Set.range (Sum.elim f g) = Set.range f ∪ Set.range g := by
  ext x
  constructor
  · rintro ⟨a | b,rfl⟩
    · exact Or.inl ⟨a,rfl⟩
    · exact Or.inr ⟨b,rfl⟩
  · rintro (⟨a,rfl⟩ | ⟨b,rfl⟩)
    · exact ⟨Sum.inl a,rfl⟩
    · exact ⟨Sum.inr b,rfl⟩

/-- The stabilized three-shear conclusion in exact cycle coordinates. This
includes injectivity for the entire new boundary list, even for infinite sets. -/
theorem stabilized_alignment (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (r : R → FreeGroup S) (z : I → FreeGroup S)
    (hr : ∀ i, wordValue v (r i) = 1) (_hz : ∀ i, wordValue v (z i) = 1)
    (hp : (wordValue v).ker = Subgroup.normalClosure (Set.range r))
    (E : BasedChains Γ R ≃ₗ[ℤ] cycles v) (B : BasedChains Γ I ≃ₗ[ℤ] cycles v)
    (hE : ∀ c, (E c : BasedChains Γ S) = relatorChainMap v r c)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v z c) :
    ∃ (r' : R → FreeGroup (S ⊕ I)) (u' : I → FreeGroup (S ⊕ I)),
      (∀ i, wordValue (Sum.elim v (fun _ : I => 1)) (r' i) = 1) ∧
      (∀ i, wordValue (Sum.elim v (fun _ : I => 1)) (u' i) = 1) ∧
      (wordValue (Sum.elim v (fun _ : I => 1))).ker =
        Subgroup.normalClosure (Set.range (Sum.elim r' u')) ∧
      Function.Injective (relatorChainMap (Sum.elim v (fun _ : I => 1)) (Sum.elim r' u')) ∧
      (∀ c, sumChainsEquiv (relatorChainMap (Sum.elim v (fun _ : I => 1)) r' c) =
        (0,-(E.trans B.symm) c)) ∧
      ∀ c, sumChainsEquiv (relatorChainMap (Sum.elim v (fun _ : I => 1)) u' c) =
        ((B c).val,0) := by
  let w : S ⊕ I → Γ := Sum.elim v (fun _ => 1)
  let r₀ : R → FreeGroup (S ⊕ I) := fun i => FreeGroup.map Sum.inl (r i)
  let u₀ : I → FreeGroup (S ⊕ I) := fun i => FreeGroup.of (.inr i)
  let A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ I := E.trans B.symm
  have hA : ChainsEquivariant A.toLinearMap := chainBasisCoordinate_equivariant v r z E B hE hB
  have hw : Function.Surjective (wordValue w) := by
    intro g
    obtain ⟨a,ha⟩ := hv g
    refine ⟨FreeGroup.map Sum.inl a,?_⟩
    have h : (wordValue w).comp (FreeGroup.map Sum.inl) = wordValue v := by
      apply FreeGroup.ext_hom
      intro s
      simp [wordValue,w]
    exact (DFunLike.congr_fun h a).trans ha
  have hr₀ : ∀ i, wordValue w (r₀ i) = 1 := fun i =>
    unitExtendedRelators_trivial v r hr (.inl i)
  have hu₀ : ∀ i, wordValue w (u₀ i) = 1 := fun i =>
    unitExtendedRelators_trivial v r hr (.inr i)
  obtain ⟨r',u',hr',hu',hN,hDr,hDu⟩ := block_word_alignment w hw r₀ u₀ hr₀ hu₀ A hA
  have hcr (c) : sumChainsEquiv (relatorChainMap w r' c) = (0,-A c) := by
    rw [hDr,LinearMap.neg_apply,LinearMap.comp_apply,map_neg]
    rw [sumChains_relatorMap_right]
    rfl
  have hcu (c) : sumChainsEquiv (relatorChainMap w u' c) = ((B c).val,0) := by
    rw [hDu,LinearMap.comp_apply,sumChains_relatorMap_left,← hE]
    simp [A]
  have hinj : Function.Injective (relatorChainMap w (Sum.elim r' u')) := by
    have hz₀ (c) (hc : relatorChainMap w (Sum.elim r' u') c = 0) : c = 0 := by
      have h := congrArg sumChainsEquiv hc
      rw [relatorChainMap_sum,map_add,hcr,hcu,map_zero] at h
      have hi : (sumChainsEquiv c).2 = 0 := by
        apply B.injective
        apply Subtype.ext
        simpa only [Prod.mk_add_mk,zero_add,Prod.fst_zero,map_zero,Submodule.coe_zero] using congrArg Prod.fst h
      have hr0 : (sumChainsEquiv c).1 = 0 := by
        apply A.injective
        simpa only [Prod.mk_add_mk,add_zero,Prod.snd_zero,neg_eq_zero,map_zero] using congrArg Prod.snd h
      apply sumChainsEquiv.injective
      exact Prod.ext (by simpa using hr0) (by simpa using hi)
    intro c d h
    apply sub_eq_zero.mp
    apply hz₀
    rw [map_sub,h,sub_self]
  refine ⟨r',u',hr',hu',?_,hinj,hcr,hcu⟩
  rw [range_sumElim,hN]
  simpa only [unitExtendedRelators,range_sumElim] using unitExtension_normalClosure (T := I) v r hp

end RelatorBlocks
end EilenbergGanea

namespace EilenbergGanea
section Reindexing
variable {Γ S T U R I : Type*} [Group Γ]

theorem relatorChainMap_reindex (v : S → Γ) (r : R → FreeGroup S) (e : I ≃ R)
    (c : BasedChains Γ I) :
    relatorChainMap v (r ∘ e) c = relatorChainMap v r (chainIndexEquiv e c) := by
  have h : relatorChainMap v (r ∘ e) = (relatorChainMap v r).comp (chainIndexEquiv e).toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    simp
  exact LinearMap.congr_fun h c

theorem chainIndexEquiv_pathChain (v : S → Γ) (w : T → Γ) (e : S ≃ T)
    (he : ∀ s, w (e s) = v s) (a : FreeGroup S) (g : Γ) :
    chainIndexEquiv e (pathChain v a g) = pathChain w (freeGroupCongr e a) g := by
  have hl : relatorChainMap w (fun s => freeGroupCongr e (FreeGroup.of s)) =
      (chainIndexEquiv e).toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨h,s⟩ n
    simp
  change (chainIndexEquiv e).toLinearMap _ = _
  rw [← hl]
  exact pathChain_hom v w (freeGroupCongr e).toMonoidHom (wordValue_congr_alphabet v w e he) a g

theorem chainIndexEquiv_relatorMap (v : S → Γ) (w : T → Γ) (e : S ≃ T)
    (he : ∀ s, w (e s) = v s) (r : R → FreeGroup S) (c : BasedChains Γ R) :
    chainIndexEquiv e (relatorChainMap v r c) =
      relatorChainMap w (fun i => freeGroupCongr e (r i)) c := by
  have h : (chainIndexEquiv e).toLinearMap.comp (relatorChainMap v r) =
      relatorChainMap w (fun i => freeGroupCongr e (r i)) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    simp [chainIndexEquiv_pathChain v w e he]
  exact LinearMap.congr_fun h c

end Reindexing
end EilenbergGanea

namespace EilenbergGanea
section ExtraProjectionAlignment
variable {Γ S T I R : Type*} [Group Γ]

omit [Group Γ] in
theorem projectExtraChains_eq_sum_snd (c : BasedChains Γ (S ⊕ T)) :
    projectExtraChains c = (sumChainsEquiv c).2 := by
  have h : projectExtraChains = (LinearMap.snd ℤ _ _).comp
      (sumChainsEquiv : BasedChains Γ (S ⊕ T) ≃ₗ[ℤ] _).toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨g,s | t⟩ n <;> simp
  exact LinearMap.congr_fun h c

omit [Group Γ] in
theorem chainIndexEquiv_sumAssoc (c : BasedChains Γ ((S ⊕ T) ⊕ I)) :
    sumChainsEquiv (chainIndexEquiv (Equiv.sumAssoc S T I) c) =
      ((sumChainsEquiv (sumChainsEquiv c).1).1,
        sumChainsEquiv.symm ((sumChainsEquiv (sumChainsEquiv c).1).2,(sumChainsEquiv c).2)) := by
  apply Prod.ext
  · ext ⟨g,s⟩
    rfl
  · apply sumChainsEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · ext ⟨g,t⟩
      rfl
    · ext ⟨g,i⟩
      rfl

omit [Group Γ] in
theorem projectExtraChains_assoc (c : BasedChains Γ ((S ⊕ T) ⊕ I)) :
    sumChainsEquiv (projectExtraChains (chainIndexEquiv (Equiv.sumAssoc S T I) c)) =
      ((sumChainsEquiv (sumChainsEquiv c).1).2,(sumChainsEquiv c).2) := by
  rw [projectExtraChains_eq_sum_snd,chainIndexEquiv_sumAssoc,LinearEquiv.apply_symm_apply]

end ExtraProjectionAlignment
end EilenbergGanea

namespace EilenbergGanea
section FinishedAlignment
variable {Γ S T R Z : Type*} [Group Γ]

/-- Reorder the two stabilization blocks into the distinguished and ordinary
lists. The projected ordinary block is exactly `(1,-A)`, not only injective. -/
theorem finish_alignment
    (v : S → Γ) (z : Z → FreeGroup S)
    (B : BasedChains Γ Z ≃ₗ[ℤ] cycles v)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v z c)
    (A : BasedChains Γ R ≃ₗ[ℤ] BasedChains Γ (Z ⊕ T))
    (r : R → FreeGroup ((S ⊕ T) ⊕ (Z ⊕ T)))
    (u : Z ⊕ T → FreeGroup ((S ⊕ T) ⊕ (Z ⊕ T)))
    (hr : ∀ i, wordValue (Sum.elim (Sum.elim v (fun _ : T => 1)) (fun _ : Z ⊕ T => 1)) (r i) = 1)
    (hu : ∀ i, wordValue (Sum.elim (Sum.elim v (fun _ : T => 1)) (fun _ : Z ⊕ T => 1)) (u i) = 1)
    (hp : (wordValue (Sum.elim (Sum.elim v (fun _ : T => 1)) (fun _ : Z ⊕ T => 1))).ker =
      Subgroup.normalClosure (Set.range (Sum.elim r u)))
    (hinj : Function.Injective (relatorChainMap
      (Sum.elim (Sum.elim v (fun _ : T => 1)) (fun _ : Z ⊕ T => 1)) (Sum.elim r u)))
    (hcr : ∀ c, sumChainsEquiv (relatorChainMap
      (Sum.elim (Sum.elim v (fun _ : T => 1)) (fun _ : Z ⊕ T => 1)) r c) = (0,-A c))
    (hcu : ∀ c, sumChainsEquiv (relatorChainMap
      (Sum.elim (Sum.elim v (fun _ : T => 1)) (fun _ : Z ⊕ T => 1)) u c) =
      ((unitExtensionBasis v B c).val,0)) :
    ∃ r' : Z ⊕ (T ⊕ R) → FreeGroup (S ⊕ (T ⊕ (Z ⊕ T))),
      (∀ i, wordValue (Sum.elim v (fun _ : T ⊕ (Z ⊕ T) => 1)) (r' i) = 1) ∧
      (wordValue (Sum.elim v (fun _ : T ⊕ (Z ⊕ T) => 1))).ker =
        Subgroup.normalClosure (Set.range r') ∧
      Function.Injective (relatorChainMap (Sum.elim v (fun _ : T ⊕ (Z ⊕ T) => 1)) r') ∧
      (∀ i, pathChain (Sum.elim v (fun _ : T ⊕ (Z ⊕ T) => 1))
        (FreeGroup.map Sum.inl (z i)) 1 =
        pathChain (Sum.elim v (fun _ : T ⊕ (Z ⊕ T) => 1)) (r' (.inl i)) 1) ∧
      (ordinaryBlockEquiv A).toLinearMap = extraRelatorMap
        (Sum.elim v (fun _ : T ⊕ (Z ⊕ T) => 1)) (fun i => r' (.inr i)) := by
  let w := Sum.elim (Sum.elim v (fun _ : T => 1)) (fun _ : Z ⊕ T => 1)
  let w' := Sum.elim v (fun _ : T ⊕ (Z ⊕ T) => 1)
  let e := Equiv.sumAssoc S T (Z ⊕ T)
  let j : Z ⊕ (T ⊕ R) ≃ R ⊕ (Z ⊕ T) := alignmentIndexEquiv
  have he : ∀ s, w' (e s) = w s := by rintro ((s | t) | i) <;> rfl
  let f : R ⊕ (Z ⊕ T) → FreeGroup (S ⊕ (T ⊕ (Z ⊕ T))) :=
    fun i => freeGroupCongr e (Sum.elim r u i)
  let r' := f ∘ j
  have hrf : ∀ i, wordValue w' (f i) = 1 := by
    intro i
    have h := DFunLike.congr_fun (wordValue_congr_alphabet w w' e he) (Sum.elim r u i)
    exact h.trans (by rcases i with i | i; exact hr i; exact hu i)
  have hpf : (wordValue w').ker = Subgroup.normalClosure (Set.range f) :=
    wordPresentation_transport w w' (freeGroupCongr e) (wordValue_congr_alphabet w w' e he) _ hp
  have hpr : (wordValue w').ker = Subgroup.normalClosure (Set.range r') := by
    rw [hpf]
    congr 1
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨j.symm i,congrArg f (j.apply_symm_apply i)⟩
    · rintro ⟨i,rfl⟩
      exact ⟨j i,rfl⟩
  have hDf (c : BasedChains Γ (R ⊕ (Z ⊕ T))) :
      relatorChainMap w' f c = chainIndexEquiv e (relatorChainMap w (Sum.elim r u) c) :=
    (chainIndexEquiv_relatorMap w w' e he _ c).symm
  have hDr (c) : relatorChainMap w' r' c =
      chainIndexEquiv e (relatorChainMap w (Sum.elim r u) (chainIndexEquiv j c)) := by
    rw [relatorChainMap_reindex,hDf]
  have hinjr : Function.Injective (relatorChainMap w' r') := by
    intro a b h
    rw [hDr,hDr] at h
    exact (chainIndexEquiv j).injective (hinj ((chainIndexEquiv e).injective h))
  have hcU (c : BasedChains Γ (Z ⊕ T)) :
      sumChainsEquiv (sumChainsEquiv (relatorChainMap w u c)).1 =
        ((B (sumChainsEquiv c).1).val,(sumChainsEquiv c).2) := by
    rw [hcu]
    change sumChainsEquiv (sumChainsEquiv.symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  have hd (i : Z) : pathChain w' (FreeGroup.map Sum.inl (z i)) 1 =
      pathChain w' (r' (.inl i)) 1 := by
    have h := hcu (Finsupp.single (1,Sum.inl i) 1)
    have h' := hcU (Finsupp.single (1,Sum.inl i) 1)
    simp only [relatorChainMap_single,one_smul,sumChainsEquiv_single_left] at h h'
    apply (sumChainsEquiv : BasedChains Γ (S ⊕ (T ⊕ (Z ⊕ T))) ≃ₗ[ℤ] _).injective
    have hh : pathChain w' (r' (.inl i)) 1 = chainIndexEquiv e (pathChain w (u (.inl i)) 1) :=
      (chainIndexEquiv_pathChain w w' e he _ _).symm
    rw [hh]
    rw [sumChains_pathChain_left,chainIndexEquiv_sumAssoc]
    rw [h]
    rw [h] at h'
    rw [h']
    simp only [hB,relatorChainMap_single,one_smul]
    change (_,0) = (_,sumChainsEquiv.symm (0 : BasedChains Γ T × BasedChains Γ (Z ⊕ T)))
    rw [map_zero]
  have hQ : (ordinaryBlockEquiv A).toLinearMap = extraRelatorMap w' (fun i => r' (.inr i)) := by
    apply Finsupp.lhom_ext
    rintro ⟨g,t | i⟩ n
    · apply sumChainsEquiv.injective
      have hh : pathChain w' (r' (.inr (.inl t))) g =
          chainIndexEquiv e (pathChain w (u (.inr t)) g) :=
        (chainIndexEquiv_pathChain w w' e he _ _).symm
      simp only [LinearEquiv.coe_coe,ordinaryBlockEquiv_value,sumChainsEquiv_single_left,
        map_zero,neg_zero,extraRelatorMap_single,hh,← map_smul]
      have hsingle : n • pathChain w (u (.inr t)) g =
          relatorChainMap w u (Finsupp.single (g,Sum.inr t) n) := by simp
      rw [hsingle,projectExtraChains_assoc,hcu]
      have hh' := hcU (Finsupp.single (g,Sum.inr t) n)
      rw [hcu] at hh'
      simp only [sumChainsEquiv_single_right,map_zero,Submodule.coe_zero] at hh'
      rw [hh']
    · apply sumChainsEquiv.injective
      have hh : pathChain w' (r' (.inr (.inr i))) g =
          chainIndexEquiv e (pathChain w (r i) g) :=
        (chainIndexEquiv_pathChain w w' e he _ _).symm
      simp only [LinearEquiv.coe_coe,ordinaryBlockEquiv_value,sumChainsEquiv_single_right,
        extraRelatorMap_single,hh,← map_smul]
      have hsingle : n • pathChain w (r i) g = relatorChainMap w r (Finsupp.single (g,i) n) := by simp
      rw [hsingle,projectExtraChains_assoc,hcr]
      simp
  exact ⟨r',fun i => hrf (j i),hpr,hinjr,hd,hQ⟩

end FinishedAlignment
end EilenbergGanea

namespace EilenbergGanea
section BoundaryBasisPresentation
variable {Γ S A R Z : Type*} [Group Γ]

/-- Full algebraic alignment. The initial and final
presentations are genuine normal-closure presentations. No finiteness of the
old generators or of either relator family is required. -/
theorem boundary_basis_presentation_alignment
    (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (z : Z → FreeGroup S) (hz : ∀ i, wordValue v (z i) = 1)
    (B : BasedChains Γ Z ≃ₗ[ℤ] cycles v)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v z c)
    (a : A → Γ) (ha : Function.Surjective (wordValue a))
    (r : R → FreeGroup A) (hr : ∀ i, wordValue a (r i) = 1)
    (hp : (wordValue a).ker = Subgroup.normalClosure (Set.range r))
    (E : BasedChains Γ R ≃ₗ[ℤ] cycles a)
    (hE : ∀ c, (E c : BasedChains Γ A) = relatorChainMap a r c) :
    ∃ (r' : Z ⊕ (A ⊕ (R ⊕ S)) → FreeGroup (S ⊕ (A ⊕ (Z ⊕ A))))
      (Q : BasedChains Γ (A ⊕ (R ⊕ S)) ≃ₗ[ℤ] BasedChains Γ (A ⊕ (Z ⊕ A))),
      (∀ i, wordValue (Sum.elim v (fun _ : A ⊕ (Z ⊕ A) => 1)) (r' i) = 1) ∧
      (wordValue (Sum.elim v (fun _ : A ⊕ (Z ⊕ A) => 1))).ker =
        Subgroup.normalClosure (Set.range r') ∧
      Function.Injective (relatorChainMap (Sum.elim v (fun _ : A ⊕ (Z ⊕ A) => 1)) r') ∧
      (∀ i, pathChain (Sum.elim v (fun _ : A ⊕ (Z ⊕ A) => 1))
        (FreeGroup.map Sum.inl (z i)) 1 =
        pathChain (Sum.elim v (fun _ : A ⊕ (Z ⊕ A) => 1)) (r' (.inl i)) 1) ∧
      Q.toLinearMap = extraRelatorMap (Sum.elim v (fun _ : A ⊕ (Z ⊕ A) => 1))
        (fun i => r' (.inr i)) := by
  obtain ⟨r₀,E₀,hr₀,hp₀,hE₀⟩ := align_generators v hv a ha r hr hp E hE
  let v₀ : S ⊕ A → Γ := Sum.elim v (fun _ => 1)
  have hv₀ : Function.Surjective (wordValue v₀) := by
    intro g
    obtain ⟨w,hw⟩ := hv g
    refine ⟨FreeGroup.map Sum.inl w,?_⟩
    have h : (wordValue v₀).comp (FreeGroup.map Sum.inl) = wordValue v := by
      apply FreeGroup.ext_hom
      intro s
      simp [wordValue,v₀]
    exact (DFunLike.congr_fun h w).trans hw
  let B₀ : BasedChains Γ (Z ⊕ A) ≃ₗ[ℤ] cycles v₀ := unitExtensionBasis v B
  let z₀ : Z ⊕ A → FreeGroup (S ⊕ A) := unitExtendedRelators z
  have hz₀ : ∀ i, wordValue v₀ (z₀ i) = 1 := unitExtendedRelators_trivial v z hz
  have hB₀ : ∀ c, (B₀ c : BasedChains Γ (S ⊕ A)) = relatorChainMap v₀ z₀ c :=
    unitExtensionBasis_value v z B hB
  obtain ⟨r₁,u₁,hr₁,hu₁,hp₁,hi₁,hcr,hcu⟩ :=
    stabilized_alignment v₀ hv₀ r₀ z₀ hr₀ hz₀ hp₀ E₀ B₀ hE₀ hB₀
  obtain ⟨r',hr',hp',hi',hd,hQ⟩ :=
    finish_alignment v z B hB (E₀.trans B₀.symm) r₁ u₁ hr₁ hu₁ hp₁ hi₁ hcr hcu
  exact ⟨r',ordinaryBlockEquiv (E₀.trans B₀.symm),hr',hp',hi',hd,hQ⟩

end BoundaryBasisPresentation
end EilenbergGanea

namespace EilenbergGanea
open scoped Quaternion
section BoundaryBasisTransport
variable {Γ S Z A R : Type*} [Group Γ] [Group.ResiduallyFinite Γ] [Fintype Z]

/-- Full algebraic content of source Theorem presentation: the only additional
input is a genuine arbitrary-alphabet presentation with boundary basis. The
separate CW-to-presentation bridge must supply that input; it is not asserted
here as a hypothesis of the main result. -/
theorem boundary_basis_small_transport_oai
    (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (z : Z → FreeGroup S) (hz : ∀ i, wordValue v (z i) = 1)
    (B : BasedChains Γ Z ≃ₗ[ℤ] cycles v)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v z c)
    (a₀ : A → Γ) (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains Γ R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains Γ A) = relatorChainMap a₀ r₀ c) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : Γ → S → SU2,
      (∀ g s, ‖(a g s : ℍ)-1‖ < η) →
      (∀ i g, pathProduct v a (z i) g = 1) →
      ∀ w : FreeGroup S, wordValue v w = 1 → ∀ g,
        pathProduct v a w g = 1 := by
  obtain ⟨r,Q,hr,hp,hinj,hd,hQ⟩ :=
    boundary_basis_presentation_alignment v hv z hz B hB a₀ ha₀ r₀ hr₀ hp₀ E hE
  exact aligned_presentation_small_transport
    (Sum.elim v (fun _ : A ⊕ (Z ⊕ A) => 1)) r z (fun _ => rfl)
    hr hz hp hinj hd Q hQ

end BoundaryBasisTransport
end EilenbergGanea


end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.EilenbergGanea.boundary_basis_small_transport_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.EilenbergGanea.boundary_basis_small_transport_oai.{u_1, u_2, u_3, u_4, u_5}
