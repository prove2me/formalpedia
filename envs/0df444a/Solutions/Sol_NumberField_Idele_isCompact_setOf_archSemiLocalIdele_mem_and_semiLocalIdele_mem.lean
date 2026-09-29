-- Prove2me | solution 1 for NumberField.Idele.isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/6963be0c-f4ec-5682-80c8-a6687cc50ab2

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm.AdelicTracePushforward
open scoped ENNReal

noncomputable section

namespace R1S83Glob

open Filter Topology
open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem continuous_semiLocalIdele (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  exact (Continuous.units_map _ (AutomorphicForm.continuous_semiLocalEval K L v)).comp
    (Continuous.units_map _ continuous_snd)

theorem continuous_archSemiLocalIdele (v : InfinitePlace K) :
    Continuous (AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v) :=
  (Continuous.units_map _ (continuous_pi fun w => continuous_apply w.1)).comp
    (Continuous.units_map _ continuous_fst)

theorem archSemiLocalIdele_apply (t : (AdeleRing (𝓞 L) L)ˣ) (w : InfinitePlace L) :
    ((AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L (w.comap (algebraMap K L)) t :
        ((w' : (w.comap (algebraMap K L)).Extension L) → w'.1.Completion)ˣ) :
          (w' : (w.comap (algebraMap K L)).Extension L) → w'.1.Completion) ⟨w, rfl⟩ =
      (t : AdeleRing (𝓞 L) L).1 w := rfl

def finCoord (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (u : (L ⊗[K] v.adicCompletion K)ˣ) :
    w.1.adicCompletion L :=
  AutomorphicForm.semiLocalHomeomorph K L v (u : L ⊗[K] v.adicCompletion K) w

theorem continuous_finCoord (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) :
    Continuous (finCoord K L v w) :=
  (continuous_apply w).comp ((AutomorphicForm.semiLocalHomeomorph K L v).continuous.comp Units.continuous_val)

theorem semiLocalHomeomorph_semiLocalEval (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L)
    (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L v (AutomorphicForm.semiLocalEval K L v a) w = a w.1 := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a)) w = a w.1
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem finCoord_semiLocalIdele (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (t : (AdeleRing (𝓞 L) L)ˣ) :
    finCoord K L v w (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t) = (t : AdeleRing (𝓞 L) L).2 w.1 :=
  semiLocalHomeomorph_semiLocalEval K L v _ w

theorem apply_mem_adicCompletionIntegers_of_mem_integralUnits (v : HeightOneSpectrum (𝓞 K))
    (t : (AdeleRing (𝓞 L) L)ˣ)
    (ht : AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)
    (w : v.Extension (𝓞 L)) :
    (t : AdeleRing (𝓞 L) L).2 w.1 ∈ w.1.adicCompletionIntegers L := by
  have h1 : ((AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) :
      L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v := by
    obtain ⟨y, hy⟩ := ht.1
    exact ⟨y, hy⟩
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers,
    Set.mem_univ_pi] at h1
  have := h1 w
  rwa [← finCoord_semiLocalIdele K L v w t]

def above (Sf : Finset (HeightOneSpectrum (𝓞 K))) : Finset (HeightOneSpectrum (𝓞 L)) :=
  HeightOneSpectrum.preimageComapFinset (𝓞 K) K L (𝓞 L) Sf

variable {K L} in
theorem mem_above_iff {Sf : Finset (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 L)} :
    w ∈ above K L Sf ↔ w.under (𝓞 K) ∈ Sf := by
  rw [above, HeightOneSpectrum.preimageComapFinset, Set.Finite.mem_toFinset, Set.mem_preimage, Finset.mem_coe]

theorem isCompact_box (Sf : Finset (HeightOneSpectrum (𝓞 K)))
    (D : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L))
    (hD : ∀ w ∈ above K L Sf, IsCompact (D w))
    (hD' : ∀ w, w ∉ above K L Sf → D w = (w.adicCompletionIntegers L : Set (w.adicCompletion L))) :
    IsCompact {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ D w} := by
  set T : Set (HeightOneSpectrum (𝓞 L)) := (↑(above K L Sf) : Set (HeightOneSpectrum (𝓞 L)))ᶜ with hT
  have hTc : Filter.cofinite ≤ 𝓟 T := by
    rw [Filter.le_principal_iff, hT]
    exact (above K L Sf).finite_toSet.compl_mem_cofinite
  let RR : HeightOneSpectrum (𝓞 L) → Type := fun w => w.adicCompletion L
  let AA : ∀ w : HeightOneSpectrum (𝓞 L), Set (RR w) := fun w =>
    (w.adicCompletionIntegers L : Set (w.adicCompletion L))
  let ι := RestrictedProduct.inclusion RR AA hTc
  set B' : Set (RestrictedProduct RR AA (𝓟 T)) := {y | ∀ w, y w ∈ D w} with hB'
  have hDall : ∀ w, IsCompact (D w) := by
    intro w
    by_cases hw : w ∈ above K L Sf
    · exact hD w hw
    · rw [hD' w hw]
      exact isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 L) L w)
  have hB'c : IsCompact B' := by
    rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := RR) (A := AA) (S := T)).isCompact_iff]
    have heq : (DFunLike.coe '' B' : Set (∀ w, RR w)) = Set.pi Set.univ D := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩ w -
        exact hy w
      · intro hx
        have hx' : ∀ᶠ w in 𝓟 T, x w ∈ AA w := by
          rw [Filter.eventually_principal]
          intro w hw
          have hwS : w ∉ above K L Sf := hw
          have := hx w (Set.mem_univ w)
          rwa [hD' w hwS] at this
        exact ⟨⟨x, hx'⟩, fun w => hx w (Set.mem_univ w), rfl⟩
    rw [heq]
    exact isCompact_univ_pi hDall
  have himage : ι '' B' = {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ D w} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩ w
      exact hy w
    · intro hx
      have hx' : ∀ᶠ w in 𝓟 T, (x : ∀ w, RR w) w ∈ AA w := by
        rw [Filter.eventually_principal]
        intro w hw
        have hwS : w ∉ above K L Sf := hw
        have := hx w
        rwa [hD' w hwS] at this
      refine ⟨⟨(x : ∀ w, RR w), hx'⟩, fun w => hx w, ?_⟩
      exact RestrictedProduct.ext _ _ fun w => rfl
  rw [← himage]
  exact hB'c.image (RestrictedProduct.continuous_inclusion hTc)

section Container

variable (A : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ)
  (Sf : Finset (HeightOneSpectrum (𝓞 K)))
  (B : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ)

def E : Set (AdeleRing (𝓞 L) L)ˣ :=
  {t : (AdeleRing (𝓞 L) L)ˣ |
      (∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ A v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sf → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ B v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
          AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)}

def archD (w : InfinitePlace L) : Set w.Completion :=
  (fun u : ((w' : (w.comap (algebraMap K L)).Extension L) → w'.1.Completion)ˣ =>
      (u : (w' : (w.comap (algebraMap K L)).Extension L) → w'.1.Completion) ⟨w, rfl⟩) '' A (w.comap (algebraMap K L))

open scoped Classical in

def finD (w : HeightOneSpectrum (𝓞 L)) : Set (w.adicCompletion L) :=
  if w ∈ above K L Sf then finCoord K L (w.under (𝓞 K)) ⟨w, rfl⟩ '' B (w.under (𝓞 K))
  else (w.adicCompletionIntegers L : Set (w.adicCompletion L))

def box : Set (AdeleRing (𝓞 L) L) :=
  {x | (∀ w : InfinitePlace L, x.1 w ∈ archD K L A w) ∧ ∀ w : HeightOneSpectrum (𝓞 L), x.2 w ∈ finD K L Sf B w}

variable {A Sf B}

theorem isCompact_box' (hA : ∀ v, IsCompact (A v)) (hB : ∀ v ∈ Sf, IsCompact (B v)) :
    IsCompact (box K L A Sf B) := by
  have h1 : IsCompact (Set.pi Set.univ (archD K L A) : Set (InfiniteAdeleRing L)) := by
    refine isCompact_univ_pi fun w => (hA _).image ?_
    exact (continuous_apply _).comp Units.continuous_val
  have h2 : IsCompact {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ finD K L Sf B w} := by
    refine isCompact_box K L Sf (finD K L Sf B) (fun w hw => ?_) (fun w hw => ?_)
    · simp only [finD, if_pos hw]
      exact (hB _ (mem_above_iff.mp hw)).image (continuous_finCoord K L _ _)
    · simp only [finD, if_neg hw]
  have h : box K L A Sf B = (Set.pi Set.univ (archD K L A) : Set (InfiniteAdeleRing L)) ×ˢ
      {x : FiniteAdeleRing (𝓞 L) L | ∀ w, x w ∈ finD K L Sf B w} := by
    ext x
    exact ⟨fun hx => ⟨fun w _ => hx.1 w, hx.2⟩, fun hx => ⟨fun w => hx.1 w (Set.mem_univ w), hx.2⟩⟩
  rw [h]
  exact h1.prod h2

theorem val_mem_box {t : (AdeleRing (𝓞 L) L)ˣ} (ht : t ∈ E K L A Sf B) : (t : AdeleRing (𝓞 L) L) ∈ box K L A Sf B := by
  obtain ⟨h1, h2, h3⟩ := ht
  refine ⟨fun w => ?_, fun w => ?_⟩
  · exact ⟨_, h1 (w.comap (algebraMap K L)), archSemiLocalIdele_apply K L t w⟩
  · by_cases hw : w ∈ above K L Sf
    · simp only [finD, if_pos hw]
      exact ⟨_, h2 _ (mem_above_iff.mp hw), finCoord_semiLocalIdele K L (w.under (𝓞 K)) ⟨w, rfl⟩ t⟩
    · simp only [finD, if_neg hw]
      exact apply_mem_adicCompletionIntegers_of_mem_integralUnits K L (w.under (𝓞 K)) t
        (h3 _ (fun h => hw (mem_above_iff.mpr h))) ⟨w, rfl⟩

theorem inv_mem_E {t : (AdeleRing (𝓞 L) L)ˣ} (ht : t ∈ E K L A Sf B) :
    t⁻¹ ∈ E K L (fun v => (A v)⁻¹) Sf (fun v => (B v)⁻¹) := by
  obtain ⟨h1, h2, h3⟩ := ht
  refine ⟨fun v => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [map_inv, Set.inv_mem_inv]
    exact h1 v
  · rw [map_inv, Set.inv_mem_inv]
    exact h2 v hv
  · rw [map_inv]
    exact inv_mem (h3 v hv)

theorem E_subset_preimage :
    E K L A Sf B ⊆ Units.embedProduct (AdeleRing (𝓞 L) L) ⁻¹'
      (box K L A Sf B ×ˢ (MulOpposite.op '' box K L (fun v => (A v)⁻¹) Sf (fun v => (B v)⁻¹))) := by
  intro t ht
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  exact ⟨val_mem_box K L ht, ⟨_, val_mem_box K L (inv_mem_E K L ht), rfl⟩⟩

theorem isClosed_integralUnits (v : HeightOneSpectrum (𝓞 K)) :
    IsClosed (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  have hS : IsClosed (AutomorphicForm.semiLocalIntegers K L v) := (AutomorphicForm.isCompact_semiLocalIntegers K L v).isClosed
  have h : (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) =
      (Units.val ⁻¹' AutomorphicForm.semiLocalIntegers K L v) ∩
        ((fun u : (L ⊗[K] v.adicCompletion K)ˣ => ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K)) ⁻¹'
          AutomorphicForm.semiLocalIntegers K L v) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage]
    show (u : L ⊗[K] v.adicCompletion K) ∈ (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range ∧
        ((u⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈
          (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).range ↔ _
    simp only [AlgHom.mem_range, AutomorphicForm.semiLocalIntegers, Set.mem_range]
  rw [h]
  exact (hS.preimage Units.continuous_val).inter (hS.preimage Units.continuous_coe_inv)

theorem isClosed_E (hA : ∀ v, IsCompact (A v)) (hB : ∀ v ∈ Sf, IsCompact (B v)) : IsClosed (E K L A Sf B) := by
  have h1 : IsClosed {t : (AdeleRing (𝓞 L) L)ˣ |
      ∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ A v} := by
    have : {t : (AdeleRing (𝓞 L) L)ˣ |
        ∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ A v} =
        ⋂ v, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v ⁻¹' A v := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact isClosed_iInter fun v => (hA v).isClosed.preimage (continuous_archSemiLocalIdele K L v)
  have h2 : IsClosed {t : (AdeleRing (𝓞 L) L)ˣ |
      ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sf → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ B v} := by
    have : {t : (AdeleRing (𝓞 L) L)ˣ |
        ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sf → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ B v} =
        ⋂ v ∈ Sf, AutomorphicForm.TransversalMeasure.semiLocalIdele K L v ⁻¹' B v := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    refine isClosed_biInter fun v hv => ?_
    haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
    haveI := t2Space_tensor K L (v.adicCompletion K)
    exact (hB v hv).isClosed.preimage (continuous_semiLocalIdele K L v)
  have h3 : IsClosed {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
      AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v} := by
    have : {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v} =
        ⋂ v ∈ (↑Sf : Set (HeightOneSpectrum (𝓞 K)))ᶜ, AutomorphicForm.TransversalMeasure.semiLocalIdele K L v ⁻¹'
          (AutomorphicForm.TransversalMeasure.integralUnits K L v : Set (L ⊗[K] v.adicCompletion K)ˣ) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe,
        SetLike.mem_coe]
    rw [this]
    exact isClosed_biInter fun v _ => (isClosed_integralUnits K L v).preimage (continuous_semiLocalIdele K L v)
  have hE : E K L A Sf B = ({t : (AdeleRing (𝓞 L) L)ˣ |
      ∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ A v} ∩
      {t : (AdeleRing (𝓞 L) L)ˣ |
        ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sf → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ B v}) ∩
      {t : (AdeleRing (𝓞 L) L)ˣ | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v} := by
    ext t
    simp only [E, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
  rw [hE]
  exact (h1.inter h2).inter h3

theorem isCompact_E (hA : ∀ v, IsCompact (A v)) (hB : ∀ v ∈ Sf, IsCompact (B v)) : IsCompact (E K L A Sf B) := by
  have hbox := isCompact_box' K L (A := A) (Sf := Sf) (B := B) hA hB
  have hbox' : IsCompact (box K L (fun v => (A v)⁻¹) Sf (fun v => (B v)⁻¹)) :=
    isCompact_box' K L (fun v => (hA v).inv) (fun v hv => by
      haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
      exact (hB v hv).inv)
  exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hbox.prod (hbox'.image MulOpposite.continuous_op))).of_isClosed_subset
    (isClosed_E K L hA hB) (E_subset_preimage K L)

end Container

end R1S83Glob

end

open scoped TensorProduct.RightActions in
attribute [local instance] AutomorphicForm.TransversalMeasure.semiLocalUnitsBorel
  AutomorphicForm.TransversalMeasure.archUnitsBorel in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (A : ∀ v : InfinitePlace K, Set (∀ w : v.Extension L, w.1.Completion)ˣ) (hA : ∀ v, IsCompact (A v))
    (Sf : Finset (HeightOneSpectrum (𝓞 K)))
    (B : ∀ v : HeightOneSpectrum (𝓞 K), Set (L ⊗[K] v.adicCompletion K)ˣ) (hB : ∀ v ∈ Sf, IsCompact (B v)) :
    IsCompact {t : (AdeleRing (𝓞 L) L)ˣ |
      (∀ v : InfinitePlace K, AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t ∈ A v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sf → AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ B v) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
          AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v)} :=
  R1S83Glob.isCompact_E K L hA hB

end S_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem
end P2MW
export P2MW.S_NumberField_Idele_isCompact_setOf_archSemiLocalIdele_mem_and_semiLocalIdele_mem (solution)
