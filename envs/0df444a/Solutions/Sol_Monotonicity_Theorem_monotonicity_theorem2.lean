-- Prove2me | solution 1 for Monotonicity_Theorem.monotonicity_theorem2
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-15T00:06:23.126018+00:00
-- url     : https://prove2.me/submissions/135efefc-45f8-4e27-8494-86b597aed267

import Definitions.Def_Monotonicity_Theorem_Framework2
import Mathlib.Tactic.FinCases
import Theorems.Thm_Monotonicity_Theorem_finite_partition_core2

open Classical
open Monotonicity_Theorem

theorem solution
    {R : Type} [LinearOrder R] [DenselyOrdered R] [NoMaxOrder R] [NoMinOrder R]
    (M : OMinimalStructure R)
    {a b : Power R 1} (hab : Lt1 a b)
    (f : DefinableFunction M
      (openInterval (Endpoint.finite (Power.coord1 a))
        (Endpoint.finite (Power.coord1 b)))
      (Set.univ : Set (Power R 1))) :
    ∃ k : Nat, ∃ p : Fin (k + 1) → Power R 1,
      p 0 = a ∧
      p (Fin.last k) = b ∧
      (∀ i : Fin k, Lt1 (p i.castSucc) (p i.succ)) ∧
      (∀ i : Fin k,
        let J : Set (Power R 1) :=
          openInterval
            (Endpoint.finite ((p i.castSucc) 0))
            (Endpoint.finite ((p i.succ) 0))
        (∀ x : {x : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) x},
          ∀ y : {y : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) y},
          J x.1 → J y.1 →
          f.toFun x = f.toFun y)
        ∨
        ((∀ x : {x : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) x},
            ∀ y : {y : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) y},
            J x.1 → J y.1 → Lt1 x.1 y.1 →
            Lt1 (f.toFun x).1 (f.toFun y).1)
          ∨
          (∀ x : {x : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) x},
            ∀ y : {y : Power R 1 //
            (openInterval (Endpoint.finite (Power.coord1 a))
              (Endpoint.finite (Power.coord1 b))) y},
            J x.1 → J y.1 → Lt1 x.1 y.1 →
            Lt1 (f.toFun y).1 (f.toFun x).1))
        ∧ J.Subset
            (ContinuousPoints
              (openInterval (Endpoint.finite (Power.coord1 a))
                (Endpoint.finite (Power.coord1 b)))
              (FunctionGraph (R := R) (m := 1) (n := 1)
                (A := openInterval (Endpoint.finite (Power.coord1 a))
                  (Endpoint.finite (Power.coord1 b)))
                (B := Set.univ)
                f.toFun))) := by
  have hsubIJ : (openInterval (Endpoint.finite (Power.coord1 a))
      (Endpoint.finite (Power.coord1 b))).Subset
      (openInterval (Endpoint.finite (Power.coord1 a))
        (Endpoint.finite (Power.coord1 b))) :=
    fun x hx => hx
  obtain ⟨k, p, hp0, hplast, hinc, hpiece⟩ :=
    Monotonicity_Theorem.finite_partition_core2 M f hab hsubIJ
  refine ⟨k, p, hp0, hplast, hinc, ?_⟩
  intro i
  rcases hpiece i with hC | hM
  · left
    obtain ⟨hconst, -⟩ := hC
    intro x y hxJ hyJ
    exact hconst x.1 x.2 hxJ y.1 y.2 hyJ
  · right
    obtain ⟨hm, hcont⟩ := hM
    refine ⟨?_, hcont⟩
    rcases hm with hincr | hdecr
    · left
      intro x y hxJ hyJ hlt
      exact hincr x.1 x.2 hxJ y.1 y.2 hyJ hlt
    · right
      intro x y hxJ hyJ hlt
      exact hdecr x.1 x.2 hxJ y.1 y.2 hyJ hlt
