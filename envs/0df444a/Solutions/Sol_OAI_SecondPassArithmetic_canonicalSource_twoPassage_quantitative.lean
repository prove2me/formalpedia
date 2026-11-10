-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalSource_twoPassage_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:01:42.33098+00:00
-- url     : https://prove2.me/submissions/61ae7944-dd1c-496c-b51f-c1e508259cb3

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceBlocks_admissible
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceBlocks_cube_norms
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceFinite_eq_raw
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceTotal_split
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalBlockCoefficient_bound
import Theorems.Thm_OAI_SecondPassArithmetic_mem_firstFrequencyDisk
import Theorems.Thm_OAI_SecondPassArithmetic_padded_rawCanonicalTwoPassage_quantitative


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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀t,g₁ t≠0→|t|≤M₁) (hg₂ : ∀t,g₂ t≠0→|t|≤M₂)
    (hV₁ : ∀t,V₁ t≠0→|t|≤N₁) (hV₂ : ∀t,V₂ t≠0→|t|≤N₂)
    (hWin₁ : ∀t,g₁ t≠0→V₁ t=1) (hWin₂ : ∀t,g₂ t≠0→V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M₁+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M₂+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
      (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (Γ Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      ‖(ell*B^2*F:ℂ)⁻¹*
        (canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    padded_rawCanonicalTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂
      hg₁ hg₂ hV₁ hV₂ hWin₁ hWin₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂ ha hadm hleft hright hsf hf
  have hcenter : canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell=
      canonicalSourceFinite p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell := by
    rw [canonicalSourceTotal_split p hp hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell hKsrc hK.le]
    ring
  rw [hcenter,canonicalSourceFinite_eq_raw]
  apply htransfer p hp hinj hcop hg hc hpr pool (canonicalSourceBlocks pool bs)
    (canonicalBlockFrequencies p K ell labels) (canonicalBlockCoefficient p hp hcop hg a Ψ₁ Ψ₂ m₁ m₂)
    (fun _=>Γ) Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂
  · exact fun q hq=>⟨hΓ,le_rfl⟩
  · exact fun q hq x hx=>canonicalBlockCoefficient_bound p hp hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ K ell hΓ hΨ₁ hΨ₂ ha q hq x hx
  · exact canonicalSourceBlocks_admissible pool bs hadm
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).1
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).2
  · intro q hq x hx
    exact hsf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).1
  · intro q hq x hx
    exact hf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).2
end OAI.SecondPassArithmetic
