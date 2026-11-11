-- Prove2me | solution 1 for OAI.ShortDraftCRT.exists_sectorwise_completions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:39:05.456203+00:00
-- url     : https://prove2.me/submissions/22e8f4c6-7ac5-4947-b8e4-49b45ca9c657

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_TranslatedFourierResidues
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualCuspDecay
import Theorems.Thm_OAI_ShortDraftCRT_exists_fixed_matrix_completion


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
open OAI.ShortDraftCRT
open scoped BigOperators Classical Matrix
variable {R : Type*} [CommRing R] [IsDomain R]
namespace OAI.ShortDraftCRT
theorem _root_.solution {ι Q : Type*} (M c : R) (hc : c≠0)
    (sector : ι→Q) (a r : ι→R)
    (hcop : ∀i,IsCoprime (a i) (c*r i))
    (hr : ∀i,IsCoprime (r i) (M*c))
    (ha : ∀i j,sector i=sector j → M*c∣a i-a j)
    (hrr : ∀i j,sector i=sector j → M∣r i-r j) :
    ∃(b d : ι→R) (C : Q→Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M})),
      (∀i,a i*d i-b i*(c*r i)=1) ∧
      ∀i,(!![a i,b i;c*r i,d i] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M}))=C (sector i) := by
  have hlocal (q : Q) :
      ∃C : Matrix (Fin 2) (Fin 2) (R⧸Ideal.span {M}),
        ∀i,sector i=q → ∃b d : R,a i*d-b*(c*r i)=1 ∧
          (!![a i,b;c*r i,d] : Matrix (Fin 2) (Fin 2) R).map
            (Ideal.Quotient.mk (Ideal.span {M}))=C := by
    by_cases hq : ∃i,sector i=q
    · obtain ⟨j,hj⟩ := hq
      obtain ⟨x,y,hxy⟩ := hcop j
      have hdet : a j*x-(-y)*(c*r j)=1 := by linear_combination hxy
      refine ⟨(!![a j,-y;c*r j,x] : Matrix (Fin 2) (Fin 2) R).map
        (Ideal.Quotient.mk (Ideal.span {M})),?_⟩
      intro i hi
      have hs : sector i=sector j := hi.trans hj.symm
      obtain ⟨b,d,hd,_,he⟩ := exists_fixed_matrix_completion M c (a j) (r j) x (-y)
        hc hdet (a i) (r i) (ha i j hs) (hrr i j hs) (hr i) (hcop i).of_mul_right_right
      exact ⟨b,d,hd,he⟩
    · refine ⟨0,?_⟩
      intro i hi
      exact False.elim (hq ⟨i,hi⟩)
  choose C hC using hlocal
  have hi (i : ι) := hC (sector i) i rfl
  choose b d hd he using hi
  exact ⟨b,d,C,hd,he⟩
end OAI.ShortDraftCRT
