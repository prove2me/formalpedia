-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.poisson_nine_terms_box
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:19:52.245088+00:00
-- url     : https://prove2.me/submissions/bb570899-1dd7-4c89-9243-90f55deecd77

import Mathlib

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.GlobalBinLoss
namespace OAI

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
open Filter
open Filter
open scoped Topology
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
open UniqueFactorizationMonoid
open scoped BigOperators

namespace CanonicalQuadraticSieve

theorem list_prod_le_power (xs : List ℝ) (U : ℝ) (hU : 0≤U)
    (hxs : ∀x∈xs, 0≤x ∧ x≤U) : xs.prod≤U^xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀y∈xs, 0≤y ∧ y≤U := fun y hy => hxs y (by simp [hy])
    simp only [List.prod_cons,List.length_cons,pow_succ]
    have hp : 0≤xs.prod := List.prod_nonneg (fun y hy => (ht y hy).1)
    exact (mul_le_mul hx.2 (ih ht) hp hU).trans_eq (mul_comm _ _)

theorem list_prod_budget (xs budget : List ℝ) (U : ℝ) (hU : 1≤U)
    (hbudget : ∀x∈budget, 0≤x ∧ x≤U) (hxs : ∀x∈xs, x∈budget) (hlen : xs.length≤8) :
    xs.prod≤U^8 := by
  apply (list_prod_le_power xs U (by linarith) (fun x hx => hbudget x (hxs x hx))).trans
  exact pow_le_pow_right₀ hU hlen

theorem poisson_nine_terms_box_oai
    (d lk ln f e vh vz dv uh du lat cd cs ct cp M N T a b eD eS tail U S : ℝ)
    (hU : 1≤U) (hS : 0≤S)
    (hbudget : ∀x∈([d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp] : List ℝ), 0≤x ∧ x≤U)
    (hM : 0≤M) (hN : 0≤N) (hT : 1≤T) (ha : 0≤a)
    (hMS : M≤S) (hNS : N≤S) (hTa : T*a≤S)
    (hb : 0≤b ∧ b≤S) (hED : 0≤eD ∧ eD≤S) (hES : 0≤eS ∧ eS≤S)
    (htail : 0≤tail ∧ tail≤S) :
    d*lk*(8*vh*ln^2*f*e*(M+a) + 8*vz*ln^2*f*e*(M+2*T*a) +
      8*ln^2*lat*dv*f*e*(M+2*T*a) + 65536*cd*eD) +
    1536*d*ct*tail +
    lk*(2*uh*d*ln^2*f*e*(4*N/T+a) + 2*d*ln^2*lat*du*f*e*(N+2*T*a) +
      32768*cs*eS) + uh*d^2*cp*b ≤ 262144*U^8*S := by
  let budget : List ℝ := [d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp]
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈budget) (hn : xs.length≤8) : xs.prod≤U^8 :=
    list_prod_budget xs budget U hU hbudget hx hn
  have hc1 : d*lk*vh*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vh,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc2 : d*lk*vz*ln^2*f*e≤U^8 := by
    have hh := hp [d,lk,vz,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc3 : d*lk*ln^2*lat*dv*f*e≤U^8 := by
    have hh := hp [d,lk,ln,ln,lat,dv,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc4 : d*lk*cd≤U^8 := by
    have hh := hp [d,lk,cd] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc5 : d*ct≤U^8 := by
    have hh := hp [d,ct] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc6 : lk*uh*d*ln^2*f*e≤U^8 := by
    have hh := hp [lk,uh,d,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc7 : lk*d*ln^2*lat*du*f*e≤U^8 := by
    have hh := hp [lk,d,ln,ln,lat,du,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc8 : lk*cs≤U^8 := by
    have hh := hp [lk,cs] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc9 : uh*d^2*cp≤U^8 := by
    have hh := hp [uh,d,d,cp] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have haS : a≤S := (by nlinarith only [ha, hT] : a≤T*a).trans hTa
  have hdiv : N/T≤N := div_le_self hN hT
  have h1 : M+a≤2*S := by linarith only [hMS, haS]
  have h2 : M+2*T*a≤3*S := by nlinarith only [hMS, hTa]
  have h3 : M+2*T*a≤3*S := h2
  have h6 : 4*N/T+a≤5*S := by rw [mul_div_assoc]; linarith only [hdiv, hNS, haS]
  have h7 : N+2*T*a≤3*S := by nlinarith only [hNS, hTa]
  have hU8 : 0≤U^8 := by positivity
  have ht1 := mul_le_mul hc1 h1 (by positivity : 0≤M+a) hU8
  have ht2 := mul_le_mul hc2 h2 (by positivity : 0≤M+2*T*a) hU8
  have ht3 := mul_le_mul hc3 h3 (by positivity : 0≤M+2*T*a) hU8
  have ht4 := mul_le_mul hc4 hED.2 hED.1 hU8
  have ht5 := mul_le_mul hc5 htail.2 htail.1 hU8
  have ht6 := mul_le_mul hc6 h6 (by positivity : 0≤4*N/T+a) hU8
  have ht7 := mul_le_mul hc7 h7 (by positivity : 0≤N+2*T*a) hU8
  have ht8 := mul_le_mul hc8 hES.2 hES.1 hU8
  have ht9 := mul_le_mul hc9 hb.2 hb.1 hU8
  nlinarith only [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, mul_nonneg hU8 hS]

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix

end

end OAI
end

theorem solution : type_of% @OAI.CanonicalQuadraticSieve.poisson_nine_terms_box_oai := @OAI.CanonicalQuadraticSieve.poisson_nine_terms_box_oai
