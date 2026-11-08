-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.retained_dual_principal_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:33:51.970052+00:00
-- url     : https://prove2.me/submissions/6cc5e774-fb15-4939-8a25-2729f197c84a

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalMajorants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
import Theorems.Thm_OAI_CanonicalQuadraticSieve_unrestrictedDualPrincipalTruncation_eq
import Theorems.Thm_OAI_CanonicalQuadraticSieve_unrestrictedDualPrincipal_error_uniform
import Theorems.Thm_OAI_CanonicalQuadraticSieve_retainedDualPrincipalSum_symmetric_truncation
import Theorems.Thm_OAI_CanonicalQuadraticSieve_norm_four_correction_terms
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_unrestricted_dual_truncated_middle
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_unrestricted_large_principal_sum
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_unrestricted_small_principal_sum


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α), 1/2 ≤ α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ),
        1≤B → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B) →
        (∀ j, Admissible (cols j) ∧ N/2 ≤ (Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ) ≤ N) →
        (∀ j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F)‖ ≤
        ‖paperRadialFourier W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
        ‖W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
        4*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
        16384*B*N*((2*M/(F*N))*((supportConstant ε hε*(N*N)^ε)*
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,herr⟩ := unrestrictedDualPrincipal_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols hray a W
  let Z := fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))
  let Y := fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T
  have hT0 : 0≤T := by linarith
  have hmain := unrestrictedDualPrincipalTruncation_eq W rows cols cols a a M F Z hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1) (fun k => (hcols k).1)
  have hsplit := retainedDualPrincipalSum_symmetric_truncation W rows cols a M F N T hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1)
  change (6:ℂ)*retainedDualPrincipalSum W rows cols a M F =
    unrestrictedDualPrincipalTruncation W rows cols cols a a M F Z +
    unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
    unrestrictedDualPrincipalErrorSum rows cols a W M F N T at hsplit
  have heq : (6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F) =
      -(paperRadialFourier W 0*unrestrictedLargePrincipalSum rows cols cols a a M F Z) -
      (W 0*unrestrictedSmallPrincipalSum rows cols cols a a M F (fun d i => (Ideal.absNorm d:ℝ)≤Z i)) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
    rw [hsplit,hmain]
    ring
  have hl := hexp.unrestricted_large_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
    rows cols cols hr hc hc hrows (fun j => ⟨(hcols j).1,(hcols j).2.2⟩)
    (fun k => ⟨(hcols k).1,(hcols k).2.2⟩) hray a a Z (fun _ => le_rfl)
  have hs := hexp.unrestricted_small_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows hcols hcols hray a a (fun d i => (Ideal.absNorm d:ℝ)≤Z i)
    (fun _ _ h => h)
  have hm := hexp.unrestricted_dual_truncated_middle hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hray (fun _ => le_rfl)
  have he := herr ε hε B N M F T hB hN hM hF hT rows cols hr hc
    (fun i => ⟨(hrows i).1.ne_zero,(hrows i).2.2⟩) hcols a W
  rw [heq]
  apply (norm_four_correction_terms _ _ _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hm) he
end OAI.CanonicalQuadraticSieve
