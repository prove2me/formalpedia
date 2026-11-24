-- Prove2me | solution 1 for GlobalTheory.TrivLocus.triv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:36.067517+00:00
-- url     : https://prove2.me/submissions/c555225a-6d0a-4110-9712-f9e38ed0ecf6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKerIffMinors
import Theorems.Thm_GlobalTheory_TrivLocus_nontrivial_sec_iff
import Theorems.Thm_GlobalTheory_TrivLocus_rs_ne_zero
import Theorems.Thm_GlobalTheory_TrivLocus_nonempty_of_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.TrivLocus
variable {X Y : Scheme.{0}}
namespace GlobalTheory.TrivLocus
theorem _root_.solution [IsIntegral X] (hX : IsField Γ(X, ⊤)) (N : LB X) (hN : ⨆ i, N.U i = ⊤) :
    Triv N ↔ Nontrivial (LB.Sec N) ∧ Nontrivial (LB.Sec (pw N (-1))) := by
  rw [nontrivial_sec_iff, nontrivial_sec_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ ⨆ i, N.U i := by rw [hN]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    have : Nonempty (N.U i) := ⟨⟨x, hi⟩⟩
    refine ⟨⟨⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩, i, (t.s i).ne_zero⟩,
      ⟨⟨fun i => ((t.s i)⁻¹).val, fun i j => ?_⟩, i, ((t.s i)⁻¹).ne_zero⟩⟩
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    rw [← zpow_neg_one (N.g i j)] at h
    exact congrArg Units.val h
  · rintro ⟨⟨s, i, hi⟩, ⟨s'', j, hj⟩⟩
    let s' : ∀ k : N.ι, Γ(X, N.U k) := s''.f
    change N.ι at j
    change s' j ≠ 0 at hj
    have hc : ∀ k l, rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k * s' k) =
        rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l * s' l) := by
      intro k l
      have h₁ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k) =
        (N.g k l).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l) := s.compat k l
      have h₂ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s' k) =
        (N.g k l ^ (-1 : ℤ)).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s' l) := s''.compat k l
      rw [map_mul, map_mul, h₁, h₂, _root_.mul_mul_mul_comm, ← Units.val_mul, zpow_neg_one, mul_inv_cancel,
        Units.val_one, _root_.one_mul]
    obtain ⟨h, hh, -⟩ := X.sheaf.existsUnique_gluing' N.U ⊤ (fun _ => homOfLE le_top) hN.ge
      (fun k => s.f k * s' k) hc
    change Γ(X, ⊤) at h
    have hh' : ∀ k, rs X (le_top : N.U k ≤ ⊤) h = s.f k * s' k := hh
    have hne : (↑(N.U i ⊓ N.U j) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen (nonempty_of_ne_zero hi) (nonempty_of_ne_zero hj)
    have hsj : s.f j ≠ 0 := by
      intro e
      have h₁ : rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i) =
        (N.g i j).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j) := s.compat i j
      rw [e, map_zero, mul_zero] at h₁
      exact rs_ne_zero _ hne hi h₁
    have : Nonempty (N.U j) := (nonempty_of_ne_zero hsj).to_subtype
    have h0 : h ≠ 0 := by
      intro e
      have := hh' j
      rw [e, map_zero] at this
      exact mul_ne_zero hsj hj this.symm
    have hu : IsUnit h := by
      obtain ⟨c, hc⟩ := hX.mul_inv_cancel h0
      exact IsUnit.of_mul_eq_one c hc
    have hs : ∀ k, IsUnit (s.f k) := fun k =>
      isUnit_of_mul_isUnit_left (hh' k ▸ hu.map (rs X (le_top : N.U k ≤ ⊤)))
    exact ⟨⟨fun k => (hs k).unit⟩, fun k l => Units.ext (s.compat k l)⟩
end GlobalTheory.TrivLocus
