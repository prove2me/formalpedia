-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalSecondRawSource_uniform_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:51:29.452617+00:00
-- url     : https://prove2.me/submissions/ef461d67-8bfe-4c24-9b5a-f907afecd887

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_HighKernelGeometry
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_QuotientTopology
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondSource_uniform_transfer
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondRawSource_eq

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open OAI.SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (b0Label)
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (outerWindow)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i) (A J : ℕ) :
    ∃ Cₐ : ℝ,0 < Cₐ ∧ ∃ Cₛ : ℝ,0 ≤ Cₛ ∧
      ∀ (R : ℝ),0 < R → ∀ (s : Finset (GlobalSecondData ι)) (T : Finset (Ideal O × O))
        (q : Ideal O × Ideal O × Ideal O) (w : GlobalSecondData ι → ℂ) (B lengthScale : ℝ)
        (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
        (z ud ue uv kap : GlobalSecondData ι → ℝ) (X₁ X₂ : ℝ),
        q.1 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
        (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,globalSecondFixedTriple p x=q) →
        (∀ x∈s,(newLabel (globalSecondTuple p x),newRow (globalSecondTuple p x))∈T) →
        (∀ a∈T,a.1 ≠ ⊥) → (∀ a∈T,(Ideal.absNorm a.1 : ℝ) ≤ lengthScale) →
        (∀ x∈s,‖w x‖*‖outerWindow V (z x) (ud x) (ue x) (uv x) (kap x)‖ ≤ B) →
        ‖globalSecondRawSource p hp hcop hg s w F Ψ₁ Ψ₂ m
          A₁ A₂ W V z ud ue uv kap X₁ X₂ R‖ ≤
        (B*Cₐ*(lengthScale*Ideal.absNorm q.1)^ε) * (Cₛ/(1+R)^A) *
          densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (fixedTripleMask m q) T (V 5) (V 6) X₁ X₂ J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := globalSecondSource_uniform_transfer p hp hcop hg hinj
    ε hε A₁ A₂ W V M hM hV A J
  refine ⟨Cₐ,hCₐ,Cₛ,hCₛ,?_⟩
  intro R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
  rw [globalSecondRawSource_eq p hp hcop hg hinj A₁ A₂ W V M hM hV s w q hfixed
    F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ R hR]
  exact htrans R hR s T q w B lengthScale F Ψ₁ Ψ₂ m z ud ue uv kap X₁ X₂ hq hB hL hs hfixed hmap ht hn hw
end OAI.SecondPassArithmetic
