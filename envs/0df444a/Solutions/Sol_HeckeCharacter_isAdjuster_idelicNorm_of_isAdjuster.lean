-- Prove2me | solution 1 for HeckeCharacter.isAdjuster_idelicNorm_of_isAdjuster
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/47261bbf-c20c-5e28-8aec-8536fe55be33

import Theorems.Thm_M4aHerbrand_idelicNorm_levelCongr_and_realPos
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

private theorem forall_realPlace_of_archSign (x : (AdeleRing (𝓞 K) K)ˣ)
    (h : ∀ τ : K →+* ℝ, archSign K τ x) (w : InfinitePlace K) (hw : w.IsReal) :
    0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      (((x : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) w) := by
  obtain ⟨τ, hτ⟩ : ∃ τ : K →+* ℝ, placeOf K τ = w := by
    refine ⟨InfinitePlace.embedding_of_isReal hw, ?_⟩
    have hcomp : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)
        = w.embedding := by
      ext y
      exact InfinitePlace.embedding_of_isReal_apply hw y
    show InfinitePlace.mk (Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)) = w
    rw [hcomp, InfinitePlace.mk_embedding]
  subst hτ
  exact h τ

private theorem archSign_of_forall_realPlace (x : (AdeleRing (𝓞 K) K)ˣ)
    (h : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
        (((x : AdeleRing (𝓞 K) K).1 : InfiniteAdeleRing K) w))
    (τ : K →+* ℝ) : archSign K τ x :=
  h (placeOf K τ) (isReal_placeOf K τ)

theorem solution (A B : Type*) [Field A]
    [NumberField A] [Field B] [NumberField B] [Algebra A B] (𝔪 : Ideal (𝓞 A))
    {v : (AdeleRing (𝓞 B) B)ˣ} {α : Bˣ} :
    HeckeCharacter.IsAdjuster B (HeckeCharacter.modulusExt A B 𝔪) v α →
      HeckeCharacter.IsAdjuster A 𝔪
        ((M4aHerbrand.GenuineDescent.genuineBaseChange A B).idelicNorm v)
        (Units.map (Algebra.norm A) α) :=
  fun h => by
    have hserved := M4aHerbrand.idelicNorm_levelCongr_and_realPos A B
      (M4aHerbrand.GenuineDescent.genuineBaseChange A B) 𝔪 v α
      (fun w hw => h.cong w hw)
      (forall_realPlace_of_archSign (K := B) _ h.sign)
    exact ⟨fun u hu => hserved.1 u hu, archSign_of_forall_realPlace (K := A) _ hserved.2⟩

end

end S_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster
end P2MW
export P2MW.S_HeckeCharacter_isAdjuster_idelicNorm_of_isAdjuster (solution)
