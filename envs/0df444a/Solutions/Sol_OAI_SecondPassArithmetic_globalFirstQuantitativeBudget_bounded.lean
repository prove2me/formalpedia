-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstQuantitativeBudget_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:41:38.637293+00:00
-- url     : https://prove2.me/submissions/9e1fe32f-70fa-43e7-ba34-0bd6696af0f1

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningBounds
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalBudgetScalar_bound
import Theorems.Thm_OAI_SecondPassArithmetic_globalFirstQuantitativeBudget_below_rank


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) :
    ∃Clo Chi : ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
      (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F Ksrc : ℝ)
      (_hstate : CanonicalStateCondition base bad Z η Ψ m labels X F Ksrc)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (side : Bool)
      (windows : Fin 7→ℝ→ℂ) (C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax : ℝ) (N J Ntail : ℕ),
      (∀u,‖base u‖≤1) → (∀i,IsCoprime (Ideal.span {p i}) bad) →
      1<Z → Real.exp 9000≤Z → 0≤η → η≤(1:ℝ)/1000 →
      0≤C → 0≤Cd → 0≤Ct → 0≤Tmax → 0≤Γ → 1≤E → 1≤U → 1≤B → 0≤H →
      Ksrc/Z^η≤U → X/B^3≤U → Real.exp 1*B≤U → H≤U → Real.exp M≤U →
      Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤Real.exp 1*B) →
      (∀b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤Real.exp 1*B) →
      globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail≤Tmax →
      (Ksrc/Z^η)/Z^(η*(N:ℝ))≤1 →
      (∀(Ψ' : ActualEisensteinCubic.O→*ℂ) (m' : ActualEisensteinCubic.O) (labels' : Finset (Ideal ActualEisensteinCubic.O)) (X' F' K' : ℝ),
        CanonicalStateCondition base bad Z η Ψ' m' labels' X' F' K' →
        fixedDepthRank Z K'<fixedDepthRank Z Ksrc → ∀s : ℝ,
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile true (windows 5)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J)) ∧
        (canonicalLogEnergy p hp hcop hg pool (normHeightTwist Ψ' s) m' labels'
          (orientedLogProfile false (windows 6)) X' K'≤E*(X'*F')^2*(1+‖s‖)^(2*J))) →
      globalFirstQuantitativeBudget p hp hcop hg pool blocks (normHeightTwist Ψ oldHeight) m windows
        C Cd Ct Γ ε (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F M H U (N+1) (2*J) Ntail side≤
        canonicalBudgetCoefficient C Cd Ct Tmax Clo Chi A₀ Vmax*
          Γ*(((X/B^3)*(Real.exp 1*B)^3)*F)*U^(deltaLoss+8*ε)*E*(1+‖oldHeight‖)^(2*J) := by
  obtain ⟨Clo,Chi,hClo,hChi,hbound⟩ := globalFirstQuantitativeBudget_below_rank deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate pool blocks side
    windows C Cd Ct Tmax Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hCd hCt hTmax hΓ hE hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ htail hterminal ih
  have hb := hbound p hp hcop hg hc hinj base bad Z η Ψ m labels X F Ksrc hstate
    pool blocks side windows C Cd Ct Γ E oldHeight B M H U A₀ Vmax N J Ntail
    hbase hpbad hZ hZbig hη hηsmall hC hΓ (zero_le_one.trans hE) hU hB hH hKU hellU hBU hHU heU
    hprogress hA hV hV₁ hV₂ hVs₁ hVs₂ hb₁ hb₂ ih
  have hX:=hstate.column_pos
  have hF : 0≤F:=zero_le_one.trans hstate.label_ge_one
  have hP : 0≤((X/B^3)*(Real.exp 1*B)^3)*F := by positivity
  have hs := canonicalBudgetScalar_bound C Cd Ct Tmax Clo Chi A₀ Vmax Γ
    (((X/B^3)*(Real.exp 1*B)^3)*F) E oldHeight (Real.exp 1*B) U deltaLoss ε
    (globalFirstTailFactor (Ksrc/Z^η) (X/B^3) (Real.exp 1*B) F U H Ntail)
    ((Ksrc/Z^η)/Z^(η*(N:ℝ))) J hC hCd hCt hTmax hClo.le hChi.le hΓ hP hE
    (by positivity) hBU hU hδ.le hε.le htail hterminal
  apply hb.trans
  convert hs using 1 <;> first | rfl | ring
end OAI.SecondPassArithmetic
