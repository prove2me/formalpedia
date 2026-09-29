-- Prove2me | solution 1 for NumberField.AdelicFourier.isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c136b571-1a77-5994-99eb-5c4722d8cd87

import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace C5F2

variable (F : Type) [Field F] [NumberField F]

theorem isLocallyConstant_finset_prod {X ι : Type*} [TopologicalSpace X] (T : Finset ι) (g : ι → X → ℂ)
    (hg : ∀ i ∈ T, IsLocallyConstant (g i)) : IsLocallyConstant (fun x => ∏ i ∈ T, g i x) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact IsLocallyConstant.const 1
  | @insert a T ha ih =>
    have h1 : IsLocallyConstant (g a) := hg a (Finset.mem_insert_self a T)
    have h2 := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have : (fun x => ∏ i ∈ insert a T, g i x) = g a * fun x => ∏ i ∈ T, g i x := by
      funext x; rw [Finset.prod_insert ha]; rfl
    rw [this]
    exact h1.mul h2

def box (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F}

theorem isOpen_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (box F S) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ => Valued.isOpen_valuationSubring _)

theorem isClosed_box (S : Finset (HeightOneSpectrum (𝓞 F))) : IsClosed (box F S) := by
  have : box F S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ (_ : v ∉ S),
      (fun x : FiniteAdeleRing (𝓞 F) F => x v) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x; simp [box]
  rw [this]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    (Valued.isClosed_valuationSubring _).preimage (RestrictedProduct.continuous_eval v)

open scoped Classical in

theorem isLocallyConstant_ite_box (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F =>
      (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F
  · refine ⟨box F S, isOpen_box F S, hx, fun x' hx' => ?_⟩
    have hx'' : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x' v ∈ v.adicCompletionIntegers F := hx'
    rw [if_pos hx'', if_pos hx]
  · refine ⟨(box F S)ᶜ, (isClosed_box F S).isOpen_compl, hx, fun x' hx' => ?_⟩
    have hx'' : ¬ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x' v ∈ v.adicCompletionIntegers F := hx'
    rw [if_neg hx'', if_neg hx]

theorem isCompact_box_of (S : Finset (HeightOneSpectrum (𝓞 F))) (C : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (hC : ∀ v ∈ S, IsCompact (C v)) :
    IsCompact {x : FiniteAdeleRing (𝓞 F) F |
      (∀ v ∈ S, x v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
  classical

  set T : Set (HeightOneSpectrum (𝓞 F)) := (↑S : Set (HeightOneSpectrum (𝓞 F)))ᶜ with hTdef
  have hT : Filter.cofinite ≤ Filter.principal T :=
    Filter.le_principal_iff.mpr (by rw [hTdef, Filter.mem_cofinite, compl_compl]; exact S.finite_toSet)
  set D : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F) := fun v =>
    if v ∈ S then C v else (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hDdef
  have hD : ∀ v, IsCompact (D v) := fun v => by
    by_cases hv : v ∈ S
    · rw [hDdef]; simp only [if_pos hv]; exact hC v hv
    · rw [hDdef]; simp only [if_neg hv]
      haveI : CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
        inferInstanceAs (CompactSpace (v.adicCompletionIntegers F))
      exact isCompact_iff_compactSpace.mpr inferInstance
  have hPD : IsCompact (Set.univ.pi D) := isCompact_univ_pi hD

  let Y := RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (Filter.principal T)
  set s : Set Y := ((↑) : Y → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) ⁻¹' Set.univ.pi D with hsdef
  have hs : IsCompact s := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal).isCompact_iff]
    have himg : ((↑) : Y → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) '' s = Set.univ.pi D := by
      refine Set.Subset.antisymm (Set.image_preimage_subset _ _) fun f hf => ?_
      have hfT : ∀ᶠ v in Filter.principal T, f v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [Filter.eventually_principal]
        intro v hv
        have hvS : v ∉ S := hv
        have := hf v (Set.mem_univ v)
        rw [hDdef] at this; simp only [if_neg hvS] at this
        exact this
      exact ⟨⟨f, hfT⟩, hf, rfl⟩
    rw [himg]; exact hPD

  have himage : RestrictedProduct.inclusion (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hT '' s
      = {x : FiniteAdeleRing (𝓞 F) F |
          (∀ v ∈ S, x v ∈ C v) ∧ ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun v hv => ?_, fun v hv => ?_⟩
      · have := hy v (Set.mem_univ v)
        rw [hDdef] at this; simp only [if_pos hv] at this
        exact this
      · have := hy v (Set.mem_univ v)
        rw [hDdef] at this; simp only [if_neg hv] at this
        exact this
    · rintro ⟨h1, h2⟩
      have hxT : ∀ᶠ v in Filter.principal T, x v ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        rw [Filter.eventually_principal]; exact fun v hv => h2 v hv
      refine ⟨⟨fun v => x v, hxT⟩, fun v _ => ?_, ?_⟩
      · by_cases hv : v ∈ S
        · show x v ∈ D v
          rw [hDdef]; simp only [if_pos hv]; exact h1 v hv
        · show x v ∈ D v
          rw [hDdef]; simp only [if_neg hv]; exact h2 v hv
      · rfl
  rw [← himage]
  exact hs.image (RestrictedProduct.continuous_inclusion hT)

open scoped Classical in
theorem main (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) ∧
      HasCompactSupport (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) := by
  have hP : IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F => ∏ v ∈ S, h v (x v)) :=
    isLocallyConstant_finset_prod S (fun v (x : FiniteAdeleRing (𝓞 F) F) => h v (x v)) fun v hv =>
      (hlc v hv).comp_continuous (RestrictedProduct.continuous_eval v)
  refine ⟨hP.mul (isLocallyConstant_ite_box F S), ?_⟩

  refine HasCompactSupport.intro (isCompact_box_of F S (fun v => tsupport (h v)) fun v hv => hcs v hv) ?_
  intro x hx
  simp only [Set.mem_setOf_eq, not_and_or, not_forall] at hx
  rcases hx with ⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩
  · rw [Finset.prod_eq_zero hv (show h v (x v) = 0 from image_eq_zero_of_notMem_tsupport hxv), zero_mul]
  · rw [if_neg (fun hall => hxv (hall v hv)), mul_zero]

end C5F2

end

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v)) (hcs : ∀ v ∈ S, HasCompactSupport (h v)) :
    IsLocallyConstant (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) ∧
      HasCompactSupport (fun x : FiniteAdeleRing (𝓞 F) F =>
        (∏ v ∈ S, h v (x v)) *
          (if ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x v ∈ v.adicCompletionIntegers F then (1 : ℂ) else 0)) :=
  C5F2.main F S h hlc hcs

end S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers
end P2MW
export P2MW.S_NumberField_AdelicFourier_isLocallyConstant_and_hasCompactSupport_prod_mul_ite_forall_mem_adicCompletionIntegers (solution)
