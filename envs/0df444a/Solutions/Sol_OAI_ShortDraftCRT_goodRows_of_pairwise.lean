-- Prove2me | solution 1 for OAI.ShortDraftCRT.goodRows_of_pairwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:31:14.967685+00:00
-- url     : https://prove2.me/submissions/4d7e6d29-98be-447b-92b2-50db8f20e15b

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Theorems.Thm_OAI_ShortDraftCRT_crossDen_eq_product
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
private theorem product_coprime_of_each (p : R) (rows : List (R × R))
    (h : ∀ ph ∈ rows, IsCoprime ph.1 p) :
    IsCoprime (rows.map Prod.fst).prod p := by
  induction rows with
  | nil => simpa using (isCoprime_one_left : IsCoprime (1 : R) p)
  | cons ph rows ih =>
      rcases ph with ⟨q, k⟩
      simp only [List.map_cons, List.prod_cons]
      exact (h (q, k) (List.mem_cons_self ..)).mul_left
        (ih (by
          intro ph hmem
          exact h ph (List.mem_cons_of_mem _ hmem)))
end ShortDraftCRT
namespace ShortDraftDescent
end ShortDraftDescent
namespace ShortDraftTrace
open Complex
open scoped ComplexConjugate
section Generic
variable (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0)
  (hconj : conj ω = ω ^ 2)
include hω hconj
end Generic
end ShortDraftTrace
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.ShortDraftCRT
open AddChar
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCRT
theorem _root_.solution (c₀ : R) (rows : List (R × R))
    (hfixed : ∀ ph ∈ rows, IsCoprime c₀ ph.1)
    (hfreq : ∀ ph ∈ rows, IsCoprime ph.2 ph.1)
    (hpair : rows.Pairwise fun x y => IsCoprime x.1 y.1) :
    GoodRows c₀ rows := by
  induction rows with
  | nil => trivial
  | cons ph rows ih =>
      rcases ph with ⟨p, h⟩
      have hpairhead : ∀ ph ∈ rows, IsCoprime p ph.1 :=
        (List.pairwise_cons.mp hpair).1
      have hpairtail : rows.Pairwise fun x y => IsCoprime x.1 y.1 :=
        (List.pairwise_cons.mp hpair).2
      have hrest : GoodRows c₀ rows := ih
        (by intro ph hmem; exact hfixed ph (List.mem_cons_of_mem _ hmem))
        (by intro ph hmem; exact hfreq ph (List.mem_cons_of_mem _ hmem))
        hpairtail
      have hprod : IsCoprime ((rows.map Prod.fst).prod) p :=
        product_coprime_of_each p rows (by
          intro ph hmem
          exact (hpairhead ph hmem).symm)
      refine ⟨hrest, hfreq (p, h) (List.mem_cons_self ..), ?_⟩
      rw [crossDen_eq_product]
      exact (hfixed (p, h) (List.mem_cons_self ..)).mul_left hprod
end OAI.ShortDraftCRT
