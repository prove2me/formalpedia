-- Prove2me | solution 1 for Nock.NPR.NPR_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:32:07.325795+00:00
-- url     : https://prove2.me/submissions/d1279ac9-e79e-4cf7-82a8-106c15383960

module
public import Definitions.Def_LeanPool_PureNock_Dyck
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.List.GetD
public import Mathlib.Tactic.FieldSimp
public import Definitions.Def_LeanPool_PureNock_NPR
public import Theorems.Thm_Nock_NPR_Phi1_cons
public import Theorems.Thm_Nock_NPR_Phi2_cons
public import Theorems.Thm_Nock_NPR_Phi3_cons

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Nock
open Nock.NPR
variable {K : Type*} [Field K]
namespace Nock.NPR
theorem _root_.solution (n nL nR : Noun) :
    Φ (K := K) n = Φ (K := K) (Noun.cell nL nR)
      ↔ ( (Φ (K := K) n).1 = (Φ (K := K) nL).1 * (Φ (K := K) nR).1
        ∧ (Φ (K := K) n).2.1 = (Φ (K := K) nL).2.1 + X ^ nL.leaves * (Φ (K := K) nR).2.1
        ∧ (Φ (K := K) n).2.2 = X * (Φ (K := K) nL).2.2 + X ^ (2 * nL.leaves - 1)
            + X ^ (2 * nL.leaves) * (Φ (K := K) nR).2.2 ) := by
  constructor
  · intro h
    rw [h]
    exact ⟨Phi1_cons nL nR, Phi2_cons nL nR, Phi3_cons nL nR⟩
  · rintro ⟨h1, h2, h3⟩
    have e1 : (Φ (K := K) n).1 = (Φ (K := K) (Noun.cell nL nR)).1 := by
      rw [h1, Phi1_cons]
    have e2 : (Φ (K := K) n).2.1 = (Φ (K := K) (Noun.cell nL nR)).2.1 := by
      rw [h2, Phi2_cons]
    have e3 : (Φ (K := K) n).2.2 = (Φ (K := K) (Noun.cell nL nR)).2.2 := by
      rw [h3, Phi3_cons]
    exact Prod.ext_iff.mpr ⟨e1, Prod.ext_iff.mpr ⟨e2, e3⟩⟩
end Nock.NPR
