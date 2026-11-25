-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.isOpenMap_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:57:46.883255+00:00
-- url     : https://prove2.me/submissions/838633d5-e6c1-4303-a61d-e110a86858cb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Topology Set DoubleCoset
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SigmaCompactSpace G]
variable {P Q : Subgroup G}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G)) (x : G)
    (hC : IsLocallyClosed (doubleCoset x (P : Set G) Q)) :
    IsOpenMap (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) := by
  let := doubleCosetAction P Q x
  have : SigmaCompactSpace P := hP.sigmaCompactSpace
  have : SigmaCompactSpace Q := hQ.sigmaCompactSpace
  have : LocallyCompactSpace (doubleCoset x (P : Set G) Q) := hC.locallyCompactSpace
  have : ContinuousSMul (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨Continuous.subtype_mk ?_ _⟩
    exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).inv)
  have : MulAction.IsPretransitive (P × Q) (doubleCoset x (P : Set G) Q) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := mem_doubleCoset.1 a.2
    obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := mem_doubleCoset.1 b.2
    refine ⟨(⟨p₂ * p₁⁻¹, P.mul_mem hp₂ (P.inv_mem hp₁)⟩, ⟨q₂⁻¹ * q₁, Q.mul_mem (Q.inv_mem hq₂) hq₁⟩), ?_⟩
    apply Subtype.ext
    show (p₂ * p₁⁻¹) * (a : G) * (q₂⁻¹ * q₁)⁻¹ = b
    rw [h₁, h₂]
    group
  have hopen := isOpenMap_smul_of_sigmaCompact (G := P × Q) (X := doubleCoset x (P : Set G) Q)
    ⟨x, mem_doubleCoset_self P Q x⟩
  let e : (P × Q) ≃ₜ (P × Q) := (Homeomorph.refl P).prodCongr (Homeomorph.inv Q)
  have : (fun pq : P × Q => (⟨(pq.1 : G) * x * pq.2,
      mem_doubleCoset.2 ⟨pq.1, pq.1.2, pq.2, pq.2.2, rfl⟩⟩ : doubleCoset x (P : Set G) Q)) =
      (fun γ : P × Q => γ • (⟨x, mem_doubleCoset_self P Q x⟩ : doubleCoset x (P : Set G) Q)) ∘ e := by
    funext pq
    apply Subtype.ext
    show (pq.1 : G) * x * pq.2 = (pq.1 : G) * x * ((pq.2⁻¹ : Q) : G)⁻¹
    simp
  rw [this]
  exact hopen.comp e.isOpenMap
end GroundTheory.Automorphic.Parabolic
