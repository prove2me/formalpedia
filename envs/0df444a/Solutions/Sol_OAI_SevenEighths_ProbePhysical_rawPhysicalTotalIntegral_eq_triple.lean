-- Prove2me | solution 1 for OAI.SevenEighths.ProbePhysical.rawPhysicalTotalIntegral_eq_triple
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T04:39:18.553033+00:00
-- url     : https://prove2.me/submissions/929d3366-321b-4613-ad9f-947b92c3b176

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_rawPhysicalMellinTerm_eq_source
import Theorems.Thm_OAI_SevenEighths_ProbePhysical_rawSourceOnLines_integrable

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.ContourShear
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

lemma sourceHeightShear_preserving : MeasurePreserving sourceHeightShear heightMeasure heightMeasure := by
  exact (measurePreserving_add_prod (volume:Measure ℝ) volume).prod (MeasurePreserving.id volume)

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.MixedFubini
namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

lemma integral_count_eq_tsum {A : Type*} [Countable A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (f : A→ℂ) (hf : Integrable f Measure.count) :
    (∫a,f a ∂Measure.count)=∑'a,f a := by
  simpa using integral_countable hf

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RawArithmetic
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

lemma rawHighCoefficient_outer_support (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (mask : NonzeroFrequency→ℂ) (x w z : ℂ) (p : RawHighIndex)
    (hp : fullHighCoefficient S D η mask x w z (rawHighEmbedding p)≠0) :
    Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2 := by
  have hb : bareIdealHighCoefficient η p.1.val p.2.1.1 p.2.1.2 p.2.2 1≠0 := by
    intro hz
    exact hp (by simp only [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,bareIdealHighSummand,hz,mul_zero,zero_mul])
  have hs : Supported p.2.2 := by
    unfold bareIdealHighCoefficient at hb
    split_ifs at hb with hh
    · exact hh.2.2.2.1
    · exact False.elim (hb rfl)
  refine ⟨hs,?_⟩
  by_contra hn
  exact hp (by simp [fullHighCoefficient,rawHighEmbedding,markedIdealHighSummand,highIdealMask,hn])

lemma rawArithmeticSeries_eq_sourceRaw (S : Finset (Ideal O)) (D : Ideal O) (η : HeckeFamily.Character)
    (C : CalibrationData) (x w z : ℂ) :
    rawArithmeticSeries S D η C x w z=
      ∑'i : SourceRawIndex S,fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val))
        x w z (sourceRawEmbedding S i) := by
  unfold rawArithmeticSeries sourceRawEmbedding
  change _ = ∑'i : {p : RawHighIndex // Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2}, _
  symm
  apply tsum_subtype_eq_of_support_subset (f:=fun p : RawHighIndex=>
    fullHighCoefficient S D η (fun H=>star (C.residueMonoid H.val)) x w z (rawHighEmbedding p))
    (s:={p : RawHighIndex | Supported p.2.2 ∧ ∀P∈S,¬P∣p.2.2})
  intro p hp
  exact rawHighCoefficient_outer_support S D η _ x w z p hp

end SevenEighths.ProbePhysical
end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Detector.RawSourceIntegral
namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local instance instCountableO_5_rde8f4c_1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance instCountableIdealO_5_rde8f4c_1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
attribute [local instance] OAI.SevenEighths.ProbePhysical.instMeasurableSpaceSourceRawIndex_2
local instance instMeasurableSingletonClassSourceRawIndex_2 (S : Finset (Ideal O)) : MeasurableSingletonClass (SourceRawIndex S) := ⟨fun _=>trivial⟩

lemma originalRawOnLines_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (i : SourceRawIndex S) (p : HeightSpace) :
    originalRawOnLines η S hS D W0 W1 X Y Z i p=
      rawSourceOnLines η S hS D W0 W1 X Y Z i (sourceHeightShear.symm p) := by
  rw [originalRawOnLines,rawPhysicalMellinTerm_eq_source η S hS hpS hbad D _ _ _ i.property.1
    i.property.2 W0 W1 X Y Z hX i.val.1]
  have he : (4:ℂ)+p.1.1*Complex.I+1-((2:ℂ)+p.1.2*Complex.I)=
      3+((p.1.1-p.1.2:ℝ):ℂ)*Complex.I := by push_cast;ring
  have hs : sourceHeightShear.symm p=((p.1.1-p.1.2,p.1.2),p.2) := rfl
  simp only [rawSourceOnLines,initialHighOnLines,he,hs,sourceRawEmbedding,Complex.ofReal_ofNat]
  ring

lemma rawPhysicalTotalIntegral_eq_source (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : SourceRawIndex S×HeightSpace,rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2
          ∂((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) := by
  unfold rawPhysicalTotalIntegral
  congr 1
  let e : SourceRawIndex S×HeightSpace ≃ᵐ SourceRawIndex S×HeightSpace :=
    (MeasurableEquiv.refl (SourceRawIndex S)).prodCongr sourceHeightShear.symm
  have hp : MeasurePreserving e ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure)
      ((Measure.count:Measure (SourceRawIndex S)).prod heightMeasure) :=
    (MeasurePreserving.id _).prod (sourceHeightShear_preserving.symm sourceHeightShear)
  have he := hp.integral_comp' (fun p : SourceRawIndex S×HeightSpace=>
    rawSourceOnLines η S hS D W0 W1 X Y Z p.1 p.2)
  refine Eq.trans ?_ he
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro p
  exact originalRawOnLines_eq_source η S hS hpS hbad D W0 W1 X Y Z hX p.1 p.2

lemma rawPhysicalTotalIntegral_eq_triple_oai (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (D : Ideal O) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    rawPhysicalTotalIntegral η S hS D W0 W1 X Y Z=
      rawSourceTripleIntegral η S hS D W0 W1 X Y Z := by
  rw [rawPhysicalTotalIntegral_eq_source η S hS hpS hbad D W0 W1 X Y Z hX]
  unfold rawSourceTripleIntegral
  congr 1
  have hi := rawSourceOnLines_integrable η S hS D W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with p hp
  rw [integral_count_eq_tsum _ hp,rawArithmeticSeries_eq_sourceRaw]
  simp only [rawSourceOnLines,initialHighOnLines,Complex.ofReal_ofNat,tsum_mul_right]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.ProbePhysical.rawPhysicalTotalIntegral_eq_triple_oai := @OAI.SevenEighths.ProbePhysical.rawPhysicalTotalIntegral_eq_triple_oai
