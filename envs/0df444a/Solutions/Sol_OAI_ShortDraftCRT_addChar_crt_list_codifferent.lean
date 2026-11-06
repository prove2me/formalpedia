-- Prove2me | solution 1 for OAI.ShortDraftCRT.addChar_crt_list_codifferent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:21.026744+00:00
-- url     : https://prove2.me/submissions/d1b79242-23db-4c92-af53-f1c14cb72c87

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Theorems.Thm_OAI_ShortDraftCRT_addChar_crt_of_isCoprime
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
private theorem list_prod_coprime_right (p : R) (ps : List R)
    (h : ∀ q ∈ ps, IsCoprime q p) : IsCoprime ps.prod p := by
  induction ps with
  | nil => simpa using (isCoprime_one_left : IsCoprime (1 : R) p)
  | cons q ps ih =>
      simp only [List.prod_cons]
      exact (h q (List.mem_cons_self ..)).mul_left
        (ih (by intro x hx; exact h x (List.mem_cons_of_mem _ hx)))
private theorem list_prod_ne_zero (ι : R →+* K) (ps : List R)
    (h : ∀ p ∈ ps, ι p ≠ 0) : ι ps.prod ≠ 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      simp only [List.prod_cons, map_mul]
      exact mul_ne_zero (h p (List.mem_cons_self ..))
        (ih (by intro q hq; exact h q (List.mem_cons_of_mem _ hq)))
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
theorem _root_.solution (ι : R →+* K) (ψ : AddChar K ℂ)
    (lam z : R) (ps : List R)
    (hlam : ι lam ≠ 0)
    (hperiod : ∀ y : R, ψ (ι y / ι lam) = 1)
    (hpair : ps.Pairwise IsCoprime)
    (hp : ∀ p ∈ ps, ι p ≠ 0) :
    ∃ ws : List R, ws.length = ps.length ∧
      ψ (ι z / (ι lam * ι ps.prod)) =
        (List.zipWith (fun p w => ψ (ι (w * z) / (ι lam * ι p))) ps ws).prod := by
  revert z hpair hp
  induction ps with
  | nil =>
      intro z _ _
      refine ⟨[], rfl, ?_⟩
      simpa using hperiod z
  | cons p ps ih =>
      intro z hpair hp
      have hhead : ∀ q ∈ ps, IsCoprime p q :=
        (List.pairwise_cons.mp hpair).1
      have htail : ps.Pairwise IsCoprime :=
        (List.pairwise_cons.mp hpair).2
      have hcop : IsCoprime ps.prod p :=
        list_prod_coprime_right p ps (by
          intro q hq
          exact (hhead q hq).symm)
      have htailnonzero : ι ps.prod ≠ 0 :=
        list_prod_ne_zero ι ps (by
          intro q hq
          exact hp q (List.mem_cons_of_mem _ hq))
      have hpnonzero : ι p ≠ 0 := hp p (List.mem_cons_self ..)
      obtain ⟨u, v, hbez, hsplit⟩ :=
        addChar_crt_of_isCoprime ι ψ p ps.prod (ι z / ι lam)
          hcop hpnonzero htailnonzero
      obtain ⟨ws, hlen, htailphase⟩ := ih (v * z) htail (by
        intro q hq
        exact hp q (List.mem_cons_of_mem _ hq))
      refine ⟨u :: ws.map (· * v), by simp [hlen], ?_⟩
      simp only [List.prod_cons, map_mul]
      have hden : ι z / (ι lam * (ι p * ι ps.prod)) =
          (ι z / ι lam) / (ι p * ι ps.prod) := by field_simp
      rw [hden]
      rw [hsplit]
      simp only [List.zipWith_cons_cons, List.prod_cons]
      have hfirst : ψ (ι u * (ι z / ι lam) / ι p) =
          ψ (ι (u * z) / (ι lam * ι p)) := by
        congr 1
        simp only [map_mul]
        field_simp
      have hsecond : ψ (ι v * (ι z / ι lam) / ι ps.prod) =
          ψ (ι (v * z) / (ι lam * ι ps.prod)) := by
        congr 1
        simp only [map_mul]
        field_simp
      rw [hfirst, hsecond, htailphase]
      simp only [map_mul]
      congr 1
      rw [List.zipWith_map_right]
      simp only [map_mul, mul_assoc]
end OAI.ShortDraftCRT
